# TinyObjLoader v3 API Design

## Overview

Version 3 introduces a modern, memory-safe API with enhanced error reporting and flexible data source support. The design centers around a `StreamReader` abstraction that enables parsing from various sources (memory, file, network) with proper bounds checking and endianness handling.

## Requirements

- **C++14 minimum** (fully compatible with C++17 and later)
- **No C++ exceptions** (compiles with `-fno-exceptions`)
- **No RTTI** (compiles with `-fno-rtti`)
- **No `std::shared_ptr`** (only `std::unique_ptr` for exclusive ownership)
- Uses C++14 features: `std::make_unique`, binary literals, digit separators, generic lambdas, `[[deprecated]]`
- C++17 optional features: `std::string_view`, `std::optional`, structured bindings

## Core Design Principles

1. **Memory Safety**: All buffer access through checked StreamReader interface
2. **Detailed Error Reporting**: Result types with error codes, no exceptions
3. **Backward Compatibility**: New API in `tinyobj::v3` namespace, existing v1/v2 APIs unchanged
4. **Zero-Copy Where Possible**: StreamReader can work directly with memory-mapped files
5. **Endianness Aware**: Support for cross-platform binary OBJ extensions
6. **Modern C++14 with Embedded Constraints**: RAII, move semantics, unique_ptr only, no exceptions/RTTI
7. **Deterministic Resource Management**: All resources managed through RAII, no garbage collection or reference counting

## Architecture

### 1. StreamReader Class

The foundation of v3 is the StreamReader abstraction that provides safe, efficient access to data streams:

```cpp
namespace tinyobj {
namespace v3 {

enum class Endianness {
    Little,
    Big,
    Native = Little  // or Big depending on platform
};

class StreamReader {
public:
    // Constructors
    StreamReader(const void* data, size_t size, Endianness endian = Endianness::Native);
    StreamReader(std::unique_ptr<uint8_t[]> owned_data, size_t size, Endianness endian = Endianness::Native);

    // Non-copyable, movable
    StreamReader(const StreamReader&) = delete;
    StreamReader& operator=(const StreamReader&) = delete;
    StreamReader(StreamReader&&) noexcept = default;
    StreamReader& operator=(StreamReader&&) noexcept = default;

    // Position management
    bool seek(size_t position);
    bool seekRelative(int64_t offset);
    size_t tell() const { return position_; }
    bool eof() const { return position_ >= size_; }
    size_t remaining() const { return size_ - position_; }

    // Primitive reads with bounds checking and endian swap
    bool readUInt8(uint8_t& value);
    bool readInt8(int8_t& value);
    bool readUInt16(uint16_t& value);
    bool readInt16(int16_t& value);
    bool readUInt32(uint32_t& value);
    bool readInt32(int32_t& value);
    bool readUInt64(uint64_t& value);
    bool readInt64(int64_t& value);
    bool readFloat(float& value);
    bool readDouble(double& value);

    // Bulk reads
    bool readBytes(void* dest, size_t count);
    bool readString(std::string& str, size_t maxLength);
    bool readLine(std::string& line, size_t maxLength = 1024*1024); // 1MB default max line

    // Zero-copy access
    bool peekBytes(const uint8_t*& ptr, size_t count);

#ifdef __cpp_lib_string_view  // C++17
    std::string_view peekStringView(size_t count);
#endif

    // Utilities
    bool skipBytes(size_t count);
    bool skipWhitespace();
    bool skipLine();

private:
    const uint8_t* data_;
    std::unique_ptr<uint8_t[]> owned_data_;  // Optional ownership
    size_t size_;
    size_t position_;
    Endianness endianness_;
    Endianness host_endianness_;

    // Helper for endian swapping
    template<typename T>
    T swapEndian(T value) const;

    bool needsSwap() const { return endianness_ != host_endianness_; }
};

// Factory functions for common scenarios (using C++14 make_unique)
auto CreateStreamReaderFromFile(const std::string& path) -> std::unique_ptr<StreamReader>;
auto CreateStreamReaderFromMemory(const void* data, size_t size) -> std::unique_ptr<StreamReader>;
auto CreateStreamReaderFromString(const std::string& content) -> std::unique_ptr<StreamReader>;

} // namespace v3
} // namespace tinyobj
```

### 2. Error Handling System

Comprehensive error reporting with context stack:

```cpp
namespace tinyobj {
namespace v3 {

enum class ErrorLevel {
    Info,
    Warning,
    Error,
    Fatal
};

struct ErrorContext {
    size_t line_number;
    size_t column_number;
    std::string file_name;     // Optional, for mtllib includes
    std::string line_content;  // The actual line that caused the error
};

class ParseError {
public:
    ParseError(ErrorLevel level, const std::string& message, const ErrorContext& context)
        : level_(level), message_(message), context_(context) {}

    ErrorLevel level() const { return level_; }
    const std::string& message() const { return message_; }
    const ErrorContext& context() const { return context_; }

    std::string toString() const;

private:
    ErrorLevel level_;
    std::string message_;
    ErrorContext context_;
};

// Result type for operations that can fail (no exceptions)
template<typename T>
class Result {
public:
    Result(T&& value) : value_(std::move(value)), has_value_(true) {}
    Result(ParseError&& error) : error_(std::move(error)), has_value_(false) {}

    bool ok() const { return has_value_; }
    bool failed() const { return !has_value_; }

    T& value() { return value_; }
    const T& value() const { return value_; }
    T&& moveValue() { return std::move(value_); }

    const ParseError& error() const { return error_; }

private:
    union {
        T value_;
        ParseError error_;
    };
    bool has_value_;
};

class ErrorStack {
public:
    void push(const ParseError& error);
    void push(ParseError&& error);
    void clear();

    bool hasErrors() const;
    bool hasWarnings() const;
    bool hasFatals() const;

    std::vector<ParseError> getErrors(ErrorLevel minLevel = ErrorLevel::Warning) const;
    std::string formatErrors(ErrorLevel minLevel = ErrorLevel::Warning) const;

    // Convenience methods
    void pushInfo(const std::string& msg, const ErrorContext& ctx);
    void pushWarning(const std::string& msg, const ErrorContext& ctx);
    void pushError(const std::string& msg, const ErrorContext& ctx);
    void pushFatal(const std::string& msg, const ErrorContext& ctx);

private:
    std::vector<ParseError> errors_;
    // No mutex - single-threaded parsing or external synchronization
};

} // namespace v3
} // namespace tinyobj
```

### 3. ObjParser Class

The main parser with improved architecture:

```cpp
namespace tinyobj {
namespace v3 {

// Configuration for parser behavior
struct ParserConfig {
    bool triangulate = true;
    bool calculate_normals = false;  // Generate normals if missing
    bool validate_indices = true;    // Check index bounds
    bool strict_mode = false;        // Fail on any warning
    size_t max_line_length = 1'024 * 1'024;  // 1MB - using C++14 digit separators
    size_t max_vertices = 100'000'000;       // 100M vertices max
    size_t max_faces = 100'000'000;          // 100M faces max
    std::string mtl_search_path = "./";
    bool use_mapbox_earcut = false;        // For triangulation

    // Memory limits
    size_t max_memory_bytes = 4ULL * 1024 * 1024 * 1024; // 4GB default

    // Performance options
    bool parallel_parsing = false;   // Use multiple threads
    size_t thread_count = 0;         // 0 = auto-detect
};

// Result object containing parsed data
class ParseResult {
public:
    bool success() const { return errors_.hasFatals() == false; }

    const attrib_t& attributes() const { return attributes_; }
    const std::vector<shape_t>& shapes() const { return shapes_; }
    const std::vector<material_t>& materials() const { return materials_; }
    const ErrorStack& errors() const { return errors_; }

    // Move accessors for zero-copy transfer
    attrib_t&& moveAttributes() { return std::move(attributes_); }
    std::vector<shape_t>&& moveShapes() { return std::move(shapes_); }
    std::vector<material_t>&& moveMaterials() { return std::move(materials_); }

    // Statistics
    struct Stats {
        size_t vertices_parsed = 0;
        size_t normals_parsed = 0;
        size_t texcoords_parsed = 0;
        size_t faces_parsed = 0;
        size_t triangles_generated = 0;
        size_t materials_loaded = 0;
        size_t bytes_processed = 0;
        double parse_time_seconds = 0.0;
    };
    const Stats& stats() const { return stats_; }

#ifdef __cpp_structured_bindings  // C++17
    // Allow structured binding: auto [attrib, shapes, materials] = result.decompose();
    auto decompose() && {
        return std::make_tuple(std::move(attributes_), std::move(shapes_), std::move(materials_));
    }
#endif

private:
    friend class ObjParser;
    attrib_t attributes_;
    std::vector<shape_t> shapes_;
    std::vector<material_t> materials_;
    ErrorStack errors_;
    Stats stats_;
};

class ObjParser {
public:
    explicit ObjParser(const ParserConfig& config = ParserConfig{});

    // Main parsing interface
    ParseResult parse(StreamReader& reader);
    ParseResult parseFromFile(const std::string& path);
    ParseResult parseFromMemory(const void* data, size_t size);
    ParseResult parseFromString(const std::string& content);

    // Streaming/callback interface for large files (no virtual, no RTTI)
    struct StreamingCallbacks {
        // Function pointers instead of virtual methods (no RTTI needed)
        void (*onVertex)(void* user_data, const real_t* xyz, const real_t* w);
        void (*onNormal)(void* user_data, const real_t* xyz);
        void (*onTexCoord)(void* user_data, const real_t* uv, const real_t* w);
        void (*onFace)(void* user_data, const index_t* indices, size_t count);
        void (*onMaterial)(void* user_data, const material_t& mat);
        void (*onGroup)(void* user_data, const std::vector<std::string>& names);
        void (*onObject)(void* user_data, const std::string& name);
        bool (*shouldContinue)(void* user_data);

        void* user_data;  // User context

        // Constructor with defaults
        StreamingCallbacks() :
            onVertex(nullptr), onNormal(nullptr), onTexCoord(nullptr),
            onFace(nullptr), onMaterial(nullptr), onGroup(nullptr),
            onObject(nullptr), shouldContinue(nullptr), user_data(nullptr) {}
    };

    bool parseStreaming(StreamReader& reader, StreamingCallbacks& callbacks);

private:
    ParserConfig config_;

    // Internal parsing state
    struct ParseState {
        ErrorContext current_context;
        std::string current_object;
        std::vector<std::string> current_groups;
        int current_material_id = -1;
        size_t line_number = 0;

        // Temporary buffers for current element
        std::vector<real_t> vertex_buffer;
        std::vector<index_t> index_buffer;

        // Index maps for relative indexing
        size_t vertex_count = 0;
        size_t normal_count = 0;
        size_t texcoord_count = 0;
    };

    // Parsing methods
    bool parseLine(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseVertex(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseNormal(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseTexCoord(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseFace(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseMaterial(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseGroup(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseObject(StreamReader& reader, ParseState& state, ParseResult& result);

    // Helper methods
    bool parseFloat(StreamReader& reader, real_t& value, ParseState& state, ErrorStack& errors);
    bool parseInt(StreamReader& reader, int& value, ParseState& state, ErrorStack& errors);
    bool parseIndices(StreamReader& reader, index_t& indices, ParseState& state, ErrorStack& errors);
    bool validateIndex(int index, size_t count, const std::string& type, ParseState& state, ErrorStack& errors);

    // Material parsing
    bool parseMtlLib(const std::string& path, ParseState& state, ParseResult& result);
};

} // namespace v3
} // namespace tinyobj
```

### 4. Integration with Existing Code

The v3 API can coexist with v1/v2 through adapter functions:

```cpp
namespace tinyobj {
namespace v3 {

// Adapter to use v3 parser through v2 interface
class [[deprecated("Use v3 API directly for new code")]] V2Adapter : public ObjReader {
public:
    bool ParseFromFile(const std::string& filename, const ObjReaderConfig& config) override {
        ParserConfig v3_config;
        v3_config.triangulate = config.triangulate;
        v3_config.mtl_search_path = config.mtl_search_path;

        ObjParser parser(v3_config);
        auto result = parser.parseFromFile(filename);

        if (result.success()) {
            attrib_ = result.moveAttributes();
            shapes_ = result.moveShapes();
            materials_ = result.moveMaterials();
            warning_ = result.errors().formatErrors(ErrorLevel::Warning);
            return true;
        }

        error_ = result.errors().formatErrors(ErrorLevel::Error);
        return false;
    }
};

// Helper to migrate from v1 API
ParseResult LoadObjV3(const char* filename, const char* mtl_basedir = nullptr) {
    ParserConfig config;
    if (mtl_basedir) {
        config.mtl_search_path = mtl_basedir;
    }
    ObjParser parser(config);
    return parser.parseFromFile(filename);
}

} // namespace v3
} // namespace tinyobj
```

## Implementation Strategy

### Phase 1: Core Infrastructure
1. Implement StreamReader with full test coverage
2. Implement ErrorStack and error handling
3. Create basic ParseResult structure

### Phase 2: Parser Implementation
1. Port existing parsing logic to use StreamReader
2. Add comprehensive error reporting at each parse point
3. Implement bounds checking for all buffer access
4. Add validation for indices and data ranges

### Phase 3: Advanced Features
1. Implement parallel parsing for large files
2. Add streaming callback interface
3. Implement memory-mapped file support
4. Add binary OBJ extension support with endianness handling

### Phase 4: Integration and Migration
1. Create v2 compatibility adapter
2. Write migration guide from v1/v2 to v3
3. Update examples to show both APIs
4. Performance benchmarking against v2

## Usage Examples

### Basic Usage

```cpp
#include "tiny_obj_loader_v3.h"

int main() {
    tinyobj::v3::ParserConfig config;
    config.triangulate = true;
    config.validate_indices = true;

    tinyobj::v3::ObjParser parser(config);
    auto result = parser.parseFromFile("model.obj");

    if (!result.success()) {
        std::cerr << "Parse errors:\n" << result.errors().formatErrors() << std::endl;
        return 1;
    }

    std::cout << "Loaded " << result.stats().vertices_parsed << " vertices\n";
    std::cout << "Loaded " << result.stats().faces_parsed << " faces\n";

    // Access data
    for (const auto& shape : result.shapes()) {
        // Process shape
    }

    return 0;
}
```

### Memory Buffer Parsing

```cpp
std::vector<uint8_t> obj_data = LoadFromNetwork();
tinyobj::v3::ObjParser parser;
auto result = parser.parseFromMemory(obj_data.data(), obj_data.size());

// C++17: Using structured bindings
#if __cplusplus >= 201703L
if (result.success()) {
    auto [attrib, shapes, materials] = std::move(result).decompose();
    // Use moved data directly
}
#endif
```

### Streaming Large Files

```cpp
// C-style callbacks for no-RTTI compatibility
struct MyContext {
    GPUBuffer& gpu_buffer;
    bool user_cancelled;
};

void onVertexCallback(void* user_data, const real_t* xyz, const real_t* w) {
    auto* ctx = static_cast<MyContext*>(user_data);
    ctx->gpu_buffer.uploadVertex(xyz);
}

bool shouldContinueCallback(void* user_data) {
    auto* ctx = static_cast<MyContext*>(user_data);
    return !ctx->user_cancelled;
}

// Setup callbacks
MyContext context{gpu_buffer, false};
tinyobj::v3::ObjParser::StreamingCallbacks callbacks;
callbacks.onVertex = onVertexCallback;
callbacks.shouldContinue = shouldContinueCallback;
callbacks.user_data = &context;

parser.parseStreaming(reader, callbacks);
```

### Custom Stream Sources

```cpp
// Custom stream reader without virtual inheritance (composition pattern)
class NetworkStreamReader {
    std::unique_ptr<tinyobj::v3::StreamReader> impl_;

public:
    NetworkStreamReader(const std::string& url) {
        auto data = fetchFromNetwork(url);
        impl_ = std::make_unique<tinyobj::v3::StreamReader>(
            std::move(data), data.size()
        );
    }

    tinyobj::v3::StreamReader& reader() { return *impl_; }
};

NetworkStreamReader net_reader("http://example.com/model.obj");
auto result = parser.parse(net_reader.reader());
```

### C++14/17 Feature Usage Examples

```cpp
// C++14: Generic lambdas for parsing callbacks
auto vertex_processor = [](auto&& vertex_data) {
    // Process any vertex type
    return process(std::forward<decltype(vertex_data)>(vertex_data));
};

// C++14: Binary literals for magic numbers
constexpr uint32_t OBJ_MAGIC = 0b01001111'01000010'01001010;  // "OBJ"

// C++14: Return type deduction
auto parseFloatArray(StreamReader& reader) {
    std::vector<real_t> values;
    // ... parsing logic
    return values;
}

// C++17: Optional for nullable results
#ifdef __cpp_lib_optional
std::optional<ParseResult> tryParse(const std::string& path) {
    if (!std::filesystem::exists(path)) {
        return std::nullopt;
    }
    return parser.parseFromFile(path);
}
#endif

// Error handling without exceptions
Result<ParseResult> safeParse(const std::string& path) {
    auto result = parser.parseFromFile(path);
    if (!result.success()) {
        return ParseError(ErrorLevel::Error,
                         "Failed to parse file",
                         ErrorContext{0, 0, path, ""});
    }
    return std::move(result);
}
```

## Benefits of V3 Design

1. **Safety**: All buffer access is bounds-checked, preventing crashes from malformed files
2. **Embedded-Friendly**: No exceptions, no RTTI, deterministic memory management
3. **Debuggability**: Detailed error messages with line numbers and context
4. **Flexibility**: StreamReader abstraction supports files, memory, network, compressed data
5. **Performance**: Zero-copy operations, no shared_ptr overhead, streaming for large files
6. **Compatibility**: Existing code continues to work, gradual migration path
7. **Portability**: Endianness handling, cross-platform, works in constrained environments
8. **Modern C++ with Constraints**: RAII, move semantics, unique_ptr only
9. **Extensible**: Easy to add new formats, validations, or transformations
10. **Predictable**: No hidden allocations, no reference counting, explicit ownership

## Testing Strategy

1. **Unit Tests**: Each StreamReader method, error case, parser component
2. **Fuzz Testing**: AFL/libfuzzer integration for robustness
3. **Regression Tests**: Ensure v3 produces identical output to v2 for valid files
4. **Performance Tests**: Benchmark against v2, ensure no regression
5. **Memory Tests**: Valgrind/ASAN validation, leak detection
6. **Stress Tests**: Large files (>1GB), many objects (>1M faces)

## Migration Guide for Users

### From V1 to V3
```cpp
// V1
tinyobj::attrib_t attrib;
std::vector<tinyobj::shape_t> shapes;
std::vector<tinyobj::material_t> materials;
std::string warn, err;
bool ret = tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, "model.obj");

// V3
auto result = tinyobj::v3::LoadObjV3("model.obj");
if (result.success()) {
    auto& attrib = result.attributes();
    auto& shapes = result.shapes();
    auto& materials = result.materials();
}
```

### From V2 to V3
```cpp
// V2
tinyobj::ObjReader reader;
reader.ParseFromFile("model.obj", config);

// V3
tinyobj::v3::ObjParser parser(config);
auto result = parser.parseFromFile("model.obj");
```

## Timeline and Deliverables

1. **Week 1-2**: StreamReader implementation and tests
2. **Week 3-4**: Error handling system and ParseResult
3. **Week 5-8**: Core parser implementation
4. **Week 9-10**: Advanced features (streaming, parallel)
5. **Week 11-12**: Integration, documentation, examples
6. **Week 13-14**: Testing, benchmarking, optimization
7. **Week 15-16**: Release preparation, migration guide

## C++14 Features Utilized (Embedded-Safe)

1. **`std::make_unique`**: Safe memory management without raw `new`
2. **Binary literals**: Clearer representation of file format constants
3. **Digit separators**: Improved readability for large numeric constants
4. **`[[deprecated]]` attribute**: Clear migration path from v2
5. **Return type deduction**: Simplified template code
6. **`constexpr` improvements**: More compile-time computation
7. **Move semantics**: Efficient resource transfer without copying

## C++17 Optional Features (Compile-Time Detection)

1. **`std::string_view`**: Zero-copy string handling when available
2. **`std::optional`**: Cleaner nullable return types (when exceptions disabled)
3. **Structured bindings**: Elegant unpacking of parse results
4. **`std::filesystem`**: Platform-independent file operations
5. **`if constexpr`**: Compile-time branching for feature detection

## Design Constraints for Embedded Systems

1. **No Dynamic Dispatch**: Function pointers instead of virtual methods
2. **No Hidden Allocations**: All allocations explicit through unique_ptr
3. **No Reference Counting**: No shared_ptr, explicit ownership transfer
4. **No Exceptions**: Result<T> types for error handling
5. **No RTTI**: No dynamic_cast, no typeid
6. **Deterministic Destruction**: RAII with predictable cleanup order
7. **Minimal Runtime**: Works with `-fno-exceptions -fno-rtti`

## Open Questions

1. ~~Should v3 require C++11 minimum, or maintain C++03 compatibility?~~ **Resolved: C++14 minimum**
2. Should binary OBJ extensions be supported in initial release?
3. Should we provide async/future-based API for network sources?
4. Memory mapping strategy for large files on different platforms?
5. ~~Should we integrate with standard library filesystem (C++17)?~~ **Resolved: Optional C++17 features with compile-time detection**