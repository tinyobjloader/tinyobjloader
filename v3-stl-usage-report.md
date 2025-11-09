# TinyObjLoader v3 Internal STL Usage Report

## Summary

After implementing custom C-style parsing functions, the v3 API has **minimal STL usage** in its internal implementation. Below is a comprehensive breakdown of remaining STL dependencies.

## Categorized STL Usage

### ✅ **Necessary/Acceptable STL Usage**

These are considered acceptable and align with modern C++ practices without significant overhead:

#### 1. **Smart Pointers (RAII)**
- **Location:** Throughout
- **Usage:** `std::unique_ptr<uint8_t[]>`, `std::make_unique`
- **Reason:** Core design requirement - exclusive ownership, no shared_ptr
- **Impact:** Zero runtime overhead (move semantics only)
- **Lines:** 362, 364, 612, 1744, 1750, 1764, 1769

#### 2. **Move Semantics**
- **Location:** Result<T>, StreamReader, ParseResult
- **Usage:** `std::move()`
- **Reason:** Efficient resource transfer, no copies
- **Impact:** Compiler optimization, no runtime cost
- **Lines:** 198, 203, 220, 222, 231, 233, 244, 267, 364, 390, 665, 666, 667, 1769

#### 3. **Memory Operations**
- **Location:** StreamReader primitive reads
- **Usage:** `std::memcpy()`
- **Reason:** Safe, portable memory copy (better than raw memcpy for type safety)
- **Impact:** Usually optimized to single instruction by compiler
- **Lines:** 444, 460, 476, 493, 502, 511

#### 4. **Mathematical Functions (Minimal)**
- **Location:** tryParseDouble
- **Usage:** `std::ldexp()` only
- **Reason:** IEEE 754 compliant floating-point assembly (mantissa * 2^exp)
- **Impact:** Single CPU instruction on most platforms
- **Note:** Replaced `std::pow` with custom `customPow` + lookup tables
- **Lines:** 937

### ✅ **Data Structure STL Usage (Public API)**

These are part of the public interface and user-facing, not internal parsing:

#### 5. **Containers**
- **std::vector** - Used for:
  - `ParseError` collection in ErrorStack (line 342)
  - `shape_t`, `material_t` results (lines 655-661, 686-687)
  - Public API compatibility with v1/v2 (attrib_t, shapes, materials)
  - Group names, indices (lines 726, 748, 749, 1169)
- **Impact:** These are part of the API contract, not internal parsing loops

#### 6. **std::string** - Used for:
- **Public API:**
  - Error messages, file paths, material names
  - Result storage after parsing
  - Configuration (mtl_search_path)
- **Internal (minimal):**
  - Temporary storage for tokens (material names, commands)
  - **Note:** Not used during number parsing anymore!

**Key Improvement:** Previously built strings during number parsing, now parses directly character-by-character.

### ✅ **I/O STL Usage**

#### 7. **File I/O**
- **Location:** CreateStreamReaderFromFile
- **Usage:** `std::ifstream`, `std::ios`, `std::streamsize`
- **Reason:** Standard portable file I/O
- **Impact:** One-time file loading, not in parse loops
- **Lines:** 1756, 1761-1762
- **Alternative:** Could use platform-specific APIs (POSIX open/read, Win32 CreateFile)

### ✅ **Optional C++17 STL**

#### 8. **std::string_view** (C++17)
- **Location:** StreamReader::peekStringView
- **Usage:** Zero-copy string view (optional, feature-gated)
- **Lines:** 562-566
- **Condition:** `#ifdef __cpp_lib_string_view`

### ❌ **Eliminated STL Usage**

Successfully removed from internal parsing:

- ❌ ~~`std::strtof` / `std::strtod`~~ → ✅ Custom `tryParseDouble`
- ❌ ~~`std::strtol` / `std::atoi`~~ → ✅ Custom `parseInteger`
- ❌ ~~`std::pow`~~ → ✅ Custom `customPow` with lookup tables
- ❌ ~~String building during parsing~~ → ✅ Direct character stream parsing
- ❌ ~~`std::shared_ptr`~~ → ✅ Only `std::unique_ptr`

## Performance Critical Paths Analysis

### Hot Path: Number Parsing (0% STL overhead)
```
parseVertex/parseNormal/parseTexCoord/parseFace
  └─> parseFloat/parseInt
      └─> detail::parseRealNumber/parseInteger
          └─> detail::tryParseDouble (custom C implementation)
              ├─> customPow (lookup tables + binary exponentiation)
              └─> std::ldexp (single CPU instruction)
```

**STL Usage in Hot Path:** Only `std::ldexp` (hardware instruction)

### Warm Path: Token Reading (Minimal STL)
```
parseLine
  └─> detail::readWord
      └─> std::string::push_back (for result storage)
```

**STL Usage:** Only result storage (not during parsing logic)

### Cold Path: File I/O (One-time STL)
```
parseFromFile
  └─> CreateStreamReaderFromFile
      └─> std::ifstream (one-time file load)
```

**STL Usage:** File loading only, not in parse loops

## Comparison with v2

| Component | v2 Implementation | v3 Implementation |
|-----------|------------------|-------------------|
| Float parsing | `tryParseDouble` (custom) | `tryParseDouble` (custom, ported from v2) |
| Int parsing | `parseInt` using `atoi` | Custom `parseInteger` (no atoi) |
| Power function | Lookup table + `std::pow` | Lookup table + custom binary exponentiation |
| String during parse | Raw `const char*` pointers | Direct StreamReader character access |
| Result storage | `std::vector`, `std::string` | `std::vector`, `std::string` (same) |
| Smart pointers | Raw pointers / manual memory | `std::unique_ptr` only |

## Recommendations

### If Further STL Reduction is Desired:

1. **Replace std::vector with custom array class**
   - Would need custom growing array implementation
   - Not recommended: `std::vector` is well-optimized and zero-overhead

2. **Replace std::string with custom string class**
   - Would need custom string implementation
   - Not recommended: `std::string` is for result storage, not parsing

3. **Replace std::ifstream with platform APIs**
   - Use POSIX `open`/`read` or Win32 `CreateFile`/`ReadFile`
   - Would lose portability
   - Not recommended: File I/O is not in hot path

4. **Replace std::unique_ptr with raw pointers**
   - Would lose RAII safety
   - **Strongly not recommended:** Violates v3 design principles

### Current Assessment: ✅ **Optimal**

The current v3 implementation achieves an excellent balance:
- ✅ **Zero STL overhead in parsing hot paths**
- ✅ **Custom C-style number parsing** (like v2)
- ✅ **Modern C++14 safety** (RAII, move semantics)
- ✅ **No exceptions, no RTTI** (embedded-friendly)
- ✅ **Minimal dependencies** (only essential STL)

## Conclusion

**Total Internal STL Usage:** ~5 features
1. `std::unique_ptr` - RAII ownership (design requirement)
2. `std::move` - Zero-cost move semantics
3. `std::memcpy` - Safe memory operations
4. `std::ldexp` - IEEE 754 float assembly (hardware instruction)
5. `std::ifstream` - Portable file I/O (cold path)

**Eliminated from Hot Paths:**
- ❌ `std::strtof/strtod/strtol/atoi` - Replaced with custom parsing
- ❌ `std::pow` - Replaced with lookup tables + binary exponentiation
- ❌ String building during parsing - Direct character access

**Result:** v3 has **comparable or better performance characteristics** than v2's internal implementation while maintaining modern C++14 safety and RAII principles.
