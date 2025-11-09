/*
The MIT License (MIT)

Copyright (c) 2012-Present, Syoyo Fujita and many contributors.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
*/

//
// TinyObjLoader v3 API
//
// Version 3.0.0:
//   - Modern C++14 API with embedded system constraints
//   - No exceptions (compiles with -fno-exceptions)
//   - No RTTI (compiles with -fno-rtti)
//   - No shared_ptr (only unique_ptr for exclusive ownership)
//   - StreamReader abstraction for flexible data sources
//   - Detailed error reporting with error stack
//   - Endianness handling for binary formats
//   - RAII-based resource management
//
// Requirements:
//   - C++14 compiler
//   - Compiles with -fno-exceptions -fno-rtti
//

#ifndef TINYOBJ_V3_HH_
#define TINYOBJ_V3_HH_

#include <cstdint>
#include <cstring>
#include <memory>
#include <string>
#include <vector>
#include <algorithm>
#include <limits>

// Include base types from v2 for compatibility
#include "tiny_obj_loader.h"

namespace tinyobj {
namespace v3 {

// ============================================================================
// Configuration and feature detection
// ============================================================================

// C++17 optional features
#ifdef __cpp_lib_string_view
#include <string_view>
#define TINYOBJ_V3_HAS_STRING_VIEW 1
#endif

#ifdef __cpp_lib_optional
#include <optional>
#define TINYOBJ_V3_HAS_OPTIONAL 1
#endif

// ============================================================================
// Endianness support
// ============================================================================

enum class Endianness : uint8_t {
    Little,
    Big,
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    Native = Big
#else
    Native = Little
#endif
};

// Endian swap utilities
namespace detail {

template<typename T>
inline T swapEndian(T value) {
    static_assert(sizeof(T) <= 8, "Type too large for endian swap");

    union {
        T value;
        uint8_t bytes[sizeof(T)];
    } src, dst;

    src.value = value;
    for (size_t i = 0; i < sizeof(T); ++i) {
        dst.bytes[i] = src.bytes[sizeof(T) - 1 - i];
    }
    return dst.value;
}

template<>
inline uint8_t swapEndian<uint8_t>(uint8_t value) {
    return value;
}

template<>
inline int8_t swapEndian<int8_t>(int8_t value) {
    return value;
}

} // namespace detail

// ============================================================================
// Error handling (no exceptions)
// ============================================================================

enum class ErrorLevel : uint8_t {
    Info,
    Warning,
    Error,
    Fatal
};

struct ErrorContext {
    size_t line_number;
    size_t column_number;
    std::string file_name;
    std::string line_content;

    ErrorContext() : line_number(0), column_number(0) {}

    ErrorContext(size_t line, size_t col, const std::string& file, const std::string& content)
        : line_number(line), column_number(col), file_name(file), line_content(content) {}
};

class ParseError {
public:
    ParseError() : level_(ErrorLevel::Error) {}

    ParseError(ErrorLevel level, const std::string& message, const ErrorContext& context)
        : level_(level), message_(message), context_(context) {}

    ErrorLevel level() const { return level_; }
    const std::string& message() const { return message_; }
    const ErrorContext& context() const { return context_; }

    std::string toString() const {
        std::string result;
        switch (level_) {
            case ErrorLevel::Info:    result = "[INFO] "; break;
            case ErrorLevel::Warning: result = "[WARN] "; break;
            case ErrorLevel::Error:   result = "[ERROR] "; break;
            case ErrorLevel::Fatal:   result = "[FATAL] "; break;
        }

        if (!context_.file_name.empty()) {
            result += context_.file_name + ":";
        }
        if (context_.line_number > 0) {
            result += std::to_string(context_.line_number) + ":";
            if (context_.column_number > 0) {
                result += std::to_string(context_.column_number) + ":";
            }
            result += " ";
        }
        result += message_;

        if (!context_.line_content.empty()) {
            result += "\n  " + context_.line_content;
        }

        return result;
    }

private:
    ErrorLevel level_;
    std::string message_;
    ErrorContext context_;
};

// Result type for operations that can fail (no exceptions)
template<typename T>
class Result {
public:
    // Construct success result
    Result(T&& value) : has_value_(true) {
        new (&storage_.value) T(std::move(value));
    }

    // Construct error result
    Result(ParseError&& error) : has_value_(false) {
        new (&storage_.error) ParseError(std::move(error));
    }

    ~Result() {
        if (has_value_) {
            storage_.value.~T();
        } else {
            storage_.error.~ParseError();
        }
    }

    // Non-copyable, movable
    Result(const Result&) = delete;
    Result& operator=(const Result&) = delete;

    Result(Result&& other) noexcept : has_value_(other.has_value_) {
        if (has_value_) {
            new (&storage_.value) T(std::move(other.storage_.value));
        } else {
            new (&storage_.error) ParseError(std::move(other.storage_.error));
        }
    }

    Result& operator=(Result&& other) noexcept {
        if (this != &other) {
            this->~Result();
            has_value_ = other.has_value_;
            if (has_value_) {
                new (&storage_.value) T(std::move(other.storage_.value));
            } else {
                new (&storage_.error) ParseError(std::move(other.storage_.error));
            }
        }
        return *this;
    }

    bool ok() const { return has_value_; }
    bool failed() const { return !has_value_; }

    T& value() { return storage_.value; }
    const T& value() const { return storage_.value; }
    T&& moveValue() { return std::move(storage_.value); }

    const ParseError& error() const { return storage_.error; }

private:
    union Storage {
        T value;
        ParseError error;

        Storage() {}
        ~Storage() {}
    } storage_;

    bool has_value_;
};

class ErrorStack {
public:
    void push(const ParseError& error) {
        errors_.push_back(error);
    }

    void push(ParseError&& error) {
        errors_.push_back(std::move(error));
    }

    void clear() {
        errors_.clear();
    }

    bool hasErrors() const {
        for (const auto& err : errors_) {
            if (err.level() >= ErrorLevel::Error) {
                return true;
            }
        }
        return false;
    }

    bool hasWarnings() const {
        for (const auto& err : errors_) {
            if (err.level() >= ErrorLevel::Warning) {
                return true;
            }
        }
        return false;
    }

    bool hasFatals() const {
        for (const auto& err : errors_) {
            if (err.level() >= ErrorLevel::Fatal) {
                return true;
            }
        }
        return false;
    }

    std::vector<ParseError> getErrors(ErrorLevel minLevel = ErrorLevel::Warning) const {
        std::vector<ParseError> result;
        for (const auto& err : errors_) {
            if (err.level() >= minLevel) {
                result.push_back(err);
            }
        }
        return result;
    }

    std::string formatErrors(ErrorLevel minLevel = ErrorLevel::Warning) const {
        std::string result;
        for (const auto& err : errors_) {
            if (err.level() >= minLevel) {
                if (!result.empty()) {
                    result += "\n";
                }
                result += err.toString();
            }
        }
        return result;
    }

    // Convenience methods
    void pushInfo(const std::string& msg, const ErrorContext& ctx) {
        push(ParseError(ErrorLevel::Info, msg, ctx));
    }

    void pushWarning(const std::string& msg, const ErrorContext& ctx) {
        push(ParseError(ErrorLevel::Warning, msg, ctx));
    }

    void pushError(const std::string& msg, const ErrorContext& ctx) {
        push(ParseError(ErrorLevel::Error, msg, ctx));
    }

    void pushFatal(const std::string& msg, const ErrorContext& ctx) {
        push(ParseError(ErrorLevel::Fatal, msg, ctx));
    }

private:
    std::vector<ParseError> errors_;
};

// ============================================================================
// StreamReader - Memory-safe buffer access with bounds checking
// ============================================================================

class StreamReader {
public:
    // Construct from external buffer (non-owning)
    StreamReader(const void* data, size_t size, Endianness endian = Endianness::Native)
        : data_(static_cast<const uint8_t*>(data))
        , owned_data_(nullptr)
        , size_(size)
        , position_(0)
        , endianness_(endian)
        , host_endianness_(Endianness::Native) {
    }

    // Construct from owned buffer (takes ownership)
    StreamReader(std::unique_ptr<uint8_t[]> owned_data, size_t size, Endianness endian = Endianness::Native)
        : data_(owned_data.get())
        , owned_data_(std::move(owned_data))
        , size_(size)
        , position_(0)
        , endianness_(endian)
        , host_endianness_(Endianness::Native) {
    }

    // Non-copyable, movable
    StreamReader(const StreamReader&) = delete;
    StreamReader& operator=(const StreamReader&) = delete;

    StreamReader(StreamReader&& other) noexcept
        : data_(other.data_)
        , owned_data_(std::move(other.owned_data_))
        , size_(other.size_)
        , position_(other.position_)
        , endianness_(other.endianness_)
        , host_endianness_(other.host_endianness_) {
        other.data_ = nullptr;
        other.size_ = 0;
        other.position_ = 0;
    }

    StreamReader& operator=(StreamReader&& other) noexcept {
        if (this != &other) {
            data_ = other.data_;
            owned_data_ = std::move(other.owned_data_);
            size_ = other.size_;
            position_ = other.position_;
            endianness_ = other.endianness_;
            host_endianness_ = other.host_endianness_;

            other.data_ = nullptr;
            other.size_ = 0;
            other.position_ = 0;
        }
        return *this;
    }

    // Position management
    bool seek(size_t position) {
        if (position > size_) {
            return false;
        }
        position_ = position;
        return true;
    }

    bool seekRelative(int64_t offset) {
        int64_t new_pos = static_cast<int64_t>(position_) + offset;
        if (new_pos < 0 || new_pos > static_cast<int64_t>(size_)) {
            return false;
        }
        position_ = static_cast<size_t>(new_pos);
        return true;
    }

    size_t tell() const { return position_; }
    bool eof() const { return position_ >= size_; }
    size_t remaining() const { return size_ - position_; }
    size_t size() const { return size_; }

    // Primitive reads with bounds checking and endian swap
    bool readUInt8(uint8_t& value) {
        if (position_ + sizeof(value) > size_) {
            return false;
        }
        value = data_[position_];
        position_ += sizeof(value);
        return true;
    }

    bool readInt8(int8_t& value) {
        return readUInt8(reinterpret_cast<uint8_t&>(value));
    }

    bool readUInt16(uint16_t& value) {
        if (position_ + sizeof(value) > size_) {
            return false;
        }
        std::memcpy(&value, data_ + position_, sizeof(value));
        if (needsSwap()) {
            value = detail::swapEndian(value);
        }
        position_ += sizeof(value);
        return true;
    }

    bool readInt16(int16_t& value) {
        return readUInt16(reinterpret_cast<uint16_t&>(value));
    }

    bool readUInt32(uint32_t& value) {
        if (position_ + sizeof(value) > size_) {
            return false;
        }
        std::memcpy(&value, data_ + position_, sizeof(value));
        if (needsSwap()) {
            value = detail::swapEndian(value);
        }
        position_ += sizeof(value);
        return true;
    }

    bool readInt32(int32_t& value) {
        return readUInt32(reinterpret_cast<uint32_t&>(value));
    }

    bool readUInt64(uint64_t& value) {
        if (position_ + sizeof(value) > size_) {
            return false;
        }
        std::memcpy(&value, data_ + position_, sizeof(value));
        if (needsSwap()) {
            value = detail::swapEndian(value);
        }
        position_ += sizeof(value);
        return true;
    }

    bool readInt64(int64_t& value) {
        return readUInt64(reinterpret_cast<uint64_t&>(value));
    }

    bool readFloat(float& value) {
        uint32_t bits;
        if (!readUInt32(bits)) {
            return false;
        }
        std::memcpy(&value, &bits, sizeof(value));
        return true;
    }

    bool readDouble(double& value) {
        uint64_t bits;
        if (!readUInt64(bits)) {
            return false;
        }
        std::memcpy(&value, &bits, sizeof(value));
        return true;
    }

    // Bulk reads
    bool readBytes(void* dest, size_t count) {
        if (position_ + count > size_) {
            return false;
        }
        std::memcpy(dest, data_ + position_, count);
        position_ += count;
        return true;
    }

    bool readString(std::string& str, size_t maxLength) {
        str.clear();
        size_t count = 0;
        while (position_ < size_ && count < maxLength) {
            uint8_t ch;
            if (!readUInt8(ch)) {
                return false;
            }
            if (ch == 0) {
                break;
            }
            str.push_back(static_cast<char>(ch));
            count++;
        }
        return true;
    }

    bool readLine(std::string& line, size_t maxLength = 1'024 * 1'024) {
        line.clear();

        // Check if we're at EOF before reading
        if (position_ >= size_) {
            return false;
        }

        size_t count = 0;
        while (position_ < size_ && count < maxLength) {
            uint8_t ch;
            if (!readUInt8(ch)) {
                return false;
            }
            if (ch == '\n') {
                break;
            }
            if (ch != '\r') {  // Skip CR in CRLF
                line.push_back(static_cast<char>(ch));
            }
            count++;
        }
        return true;
    }

    // Zero-copy access
    bool peekBytes(const uint8_t*& ptr, size_t count) {
        if (position_ + count > size_) {
            return false;
        }
        ptr = data_ + position_;
        return true;
    }

#ifdef TINYOBJ_V3_HAS_STRING_VIEW
    std::string_view peekStringView(size_t count) {
        if (position_ + count > size_) {
            return std::string_view();
        }
        return std::string_view(reinterpret_cast<const char*>(data_ + position_), count);
    }
#endif

    // Utilities
    bool skipBytes(size_t count) {
        if (position_ + count > size_) {
            return false;
        }
        position_ += count;
        return true;
    }

    bool skipWhitespace() {
        while (position_ < size_) {
            uint8_t ch = data_[position_];
            if (ch != ' ' && ch != '\t' && ch != '\r') {
                break;
            }
            position_++;
        }
        return true;
    }

    bool skipLine() {
        while (position_ < size_) {
            uint8_t ch = data_[position_];
            position_++;
            if (ch == '\n') {
                break;
            }
        }
        return true;
    }

    // Peek current character without advancing
    bool peekChar(char& ch) const {
        if (position_ >= size_) {
            return false;
        }
        ch = static_cast<char>(data_[position_]);
        return true;
    }

private:
    const uint8_t* data_;
    std::unique_ptr<uint8_t[]> owned_data_;
    size_t size_;
    size_t position_;
    Endianness endianness_;
    Endianness host_endianness_;

    bool needsSwap() const {
        return endianness_ != host_endianness_;
    }
};

// ============================================================================
// File Callback System (replaces std::ifstream)
// ============================================================================

// File read callback - user implements this to load files
// Returns: pointer to file data (owned by caller), or nullptr on failure
// out_size: set to size of file data in bytes
// filepath: path to file to load
// user_data: user context pointer
typedef const char* (*FileReadCallback)(const char* filepath, size_t* out_size, void* user_data);

// File free callback - user implements this to free file data
// data: pointer returned by FileReadCallback
// user_data: user context pointer
typedef void (*FileFreeCallback)(const char* data, void* user_data);

struct FileCallbacks {
    FileReadCallback read_fn;
    FileFreeCallback free_fn;
    void* user_data;

    FileCallbacks()
        : read_fn(nullptr), free_fn(nullptr), user_data(nullptr) {}
};

// ============================================================================
// Parser Configuration
// ============================================================================

struct ParserConfig {
    bool triangulate = true;
    bool calculate_normals = false;
    bool validate_indices = true;
    bool strict_mode = false;
    size_t max_line_length = 1'024 * 1'024;  // 1MB
    size_t max_vertices = 100'000'000;       // 100M vertices max
    size_t max_faces = 100'000'000;          // 100M faces max
    std::string mtl_search_path = "./";
    bool use_mapbox_earcut = false;

    // Memory limits
    size_t max_memory_bytes = 4ULL * 1'024 * 1'024 * 1'024;  // 4GB default

    // File I/O callbacks (replaces std::ifstream)
    FileCallbacks file_callbacks;

    ParserConfig() = default;
};

// ============================================================================
// Parse Result
// ============================================================================

class ParseResult {
public:
    ParseResult() = default;

    bool success() const { return !errors_.hasFatals(); }

    const attrib_t& attributes() const { return attributes_; }
    const std::vector<shape_t>& shapes() const { return shapes_; }
    const std::vector<material_t>& materials() const { return materials_; }
    const ErrorStack& errors() const { return errors_; }

    attrib_t& attributes() { return attributes_; }
    std::vector<shape_t>& shapes() { return shapes_; }
    std::vector<material_t>& materials() { return materials_; }
    ErrorStack& errors() { return errors_; }

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
    Stats& stats() { return stats_; }

private:
    attrib_t attributes_;
    std::vector<shape_t> shapes_;
    std::vector<material_t> materials_;
    ErrorStack errors_;
    Stats stats_;
};

// ============================================================================
// ObjParser - Main parser class
// ============================================================================

class ObjParser {
public:
    explicit ObjParser(const ParserConfig& config = ParserConfig{})
        : config_(config) {
    }

    // Main parsing interface
    ParseResult parse(StreamReader& reader);

    // Parse from memory buffer (const char* input)
    ParseResult parseFromMemory(const void* data, size_t size);
    ParseResult parseFromString(const std::string& content);

    // Streaming/callback interface for large files (no virtual, no RTTI)
    struct StreamingCallbacks {
        // Function pointers instead of virtual methods
        void (*onVertex)(void* user_data, const real_t* xyz, const real_t* w);
        void (*onNormal)(void* user_data, const real_t* xyz);
        void (*onTexCoord)(void* user_data, const real_t* uv, const real_t* w);
        void (*onFace)(void* user_data, const index_t* indices, size_t count);
        void (*onMaterial)(void* user_data, const material_t& mat);
        void (*onGroup)(void* user_data, const std::vector<std::string>& names);
        void (*onObject)(void* user_data, const std::string& name);
        bool (*shouldContinue)(void* user_data);

        void* user_data;

        StreamingCallbacks()
            : onVertex(nullptr), onNormal(nullptr), onTexCoord(nullptr)
            , onFace(nullptr), onMaterial(nullptr), onGroup(nullptr)
            , onObject(nullptr), shouldContinue(nullptr)
            , user_data(nullptr) {
        }
    };

    bool parseStreaming(StreamReader& reader, StreamingCallbacks& callbacks);

private:
    ParserConfig config_;

    // Internal parsing state (no heap allocation)
    struct ParseState {
        ErrorContext current_context;
        std::string current_object;
        std::vector<std::string> current_groups;
        int current_material_id = -1;
        int current_shape_index = -1;
        unsigned int current_smoothing_group_id = 0;
        size_t line_number = 0;

        // Index counts for relative indexing
        size_t vertex_count = 0;
        size_t normal_count = 0;
        size_t texcoord_count = 0;
    };

    // Parsing implementation
    bool parseLine(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseVertex(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseNormal(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseTexCoord(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseFace(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseLinePrimitive(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parsePointPrimitive(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseUsemtl(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseMtllib(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseGroup(StreamReader& reader, ParseState& state, ParseResult& result);
    bool parseObject(StreamReader& reader, ParseState& state, ParseResult& result);

    // Helper methods
    bool parseFloat(StreamReader& reader, real_t& value, ParseState& state, ErrorStack& errors);
    bool parseInt(StreamReader& reader, int& value, ParseState& state, ErrorStack& errors);
    bool parseIndex(StreamReader& reader, index_t& idx, ParseState& state, ErrorStack& errors);
    int fixIndex(int idx, size_t count, ParseState& state, ErrorStack& errors);

    // Material parsing
    bool parseMaterialFile(const std::string& filepath, ParseState& state, ParseResult& result);
    bool parseMaterialLine(const std::string& cmd, StreamReader& reader, material_t& current_mat, ParseState& state, ParseResult& result);
    bool parseTextureOption(StreamReader& reader, texture_option_t& texopt, ParseState& state, ErrorStack& errors);
};

// ============================================================================
// Implementation Section
// ============================================================================

namespace detail {

// Macros from v2
#define IS_SPACE(x) (((x) == ' ') || ((x) == '\t'))
#define IS_DIGIT(x) (static_cast<unsigned int>((x) - '0') < static_cast<unsigned int>(10))
#define IS_NEW_LINE(x) (((x) == '\r') || ((x) == '\n') || ((x) == '\0'))

// Custom power of 10 lookup table (avoids std::pow for small exponents)
static const double kPow10[] = {
    1.0, 10.0, 100.0, 1000.0, 10000.0, 100000.0, 1000000.0,
    10000000.0, 100000000.0, 1000000000.0, 10000000000.0,
    100000000000.0, 1000000000000.0, 10000000000000.0,
    100000000000000.0, 1000000000000000.0
};

static const double kPow10Inv[] = {
    1.0, 0.1, 0.01, 0.001, 0.0001, 0.00001, 0.000001, 0.0000001,
};

// Powers of 2 for ldexp implementation
static const double kPow2Positive[] = {
    1.0,                    // 2^0
    2.0,                    // 2^1
    4.0,                    // 2^2
    8.0,                    // 2^3
    16.0,                   // 2^4
    32.0,                   // 2^5
    64.0,                   // 2^6
    128.0,                  // 2^7
    256.0,                  // 2^8
    512.0,                  // 2^9
    1024.0,                 // 2^10
    2048.0,                 // 2^11
    4096.0,                 // 2^12
    8192.0,                 // 2^13
    16384.0,                // 2^14
    32768.0,                // 2^15
    65536.0,                // 2^16
    131072.0,               // 2^17
    262144.0,               // 2^18
    524288.0,               // 2^19
    1048576.0,              // 2^20
    2097152.0,              // 2^21
    4194304.0,              // 2^22
    8388608.0,              // 2^23
    16777216.0,             // 2^24
    33554432.0,             // 2^25
    67108864.0,             // 2^26
    134217728.0,            // 2^27
    268435456.0,            // 2^28
    536870912.0,            // 2^29
    1073741824.0,           // 2^30
    2147483648.0,           // 2^31
};

static const double kPow2Negative[] = {
    1.0,                    // 2^0
    0.5,                    // 2^-1
    0.25,                   // 2^-2
    0.125,                  // 2^-3
    0.0625,                 // 2^-4
    0.03125,                // 2^-5
    0.015625,               // 2^-6
    0.0078125,              // 2^-7
    0.00390625,             // 2^-8
    0.001953125,            // 2^-9
    0.0009765625,           // 2^-10
    0.00048828125,          // 2^-11
    0.000244140625,         // 2^-12
    0.0001220703125,        // 2^-13
    0.00006103515625,       // 2^-14
    0.000030517578125,      // 2^-15
    0.0000152587890625,     // 2^-16
};

// Custom ldexp: x * 2^exp (using only +, -, *, /)
// Replaces std::ldexp with pure arithmetic operations
inline double customLdexp(double x, int exp) {
    if (exp == 0) return x;

    // Handle negative exponents
    if (exp < 0) {
        exp = -exp;
        // Use lookup table for small exponents
        if (exp < 17) {
            return x * kPow2Negative[exp];
        }
        // For larger exponents, use repeated division
        while (exp >= 32) {
            x = x / 2147483648.0;  // Divide by 2^31
            exp -= 31;
        }
        if (exp > 0 && exp < 32) {
            x = x * kPow2Negative[exp];
        }
        return x;
    }

    // Positive exponents
    // Use lookup table for small exponents
    if (exp < 32) {
        return x * kPow2Positive[exp];
    }

    // For larger exponents, use repeated multiplication
    while (exp >= 32) {
        x = x * 2147483648.0;  // Multiply by 2^31
        exp -= 31;
    }
    if (exp > 0 && exp < 32) {
        x = x * kPow2Positive[exp];
    }
    return x;
}

// Custom pow function for small integer exponents (using only *, /)
inline double customPow(double base, int exp) {
    if (exp == 0) return 1.0;
    if (exp < 0) {
        base = 1.0 / base;
        exp = -exp;
    }

    // Use lookup table for pow(10, exp)
    if (base == 10.0 && exp >= 0 && exp < 16) {
        return kPow10[exp];
    }

    // Use lookup table for pow(2, exp)
    if (base == 2.0 && exp >= 0 && exp < 32) {
        return kPow2Positive[exp];
    }

    // Binary exponentiation using only multiplication
    double result = 1.0;
    while (exp > 0) {
        if (exp & 1) result = result * base;
        base = base * base;
        exp >>= 1;
    }
    return result;
}

// Helper to skip whitespace
inline void skipSpaces(StreamReader& reader) {
    char ch;
    while (reader.peekChar(ch)) {
        if (!IS_SPACE(ch)) {
            break;
        }
        reader.skipBytes(1);
    }
}

// Custom tryParseDouble implementation (based on v2's implementation)
// This avoids std::strtod and std::pow for better control
inline bool tryParseDouble(StreamReader& reader, double& result) {
    skipSpaces(reader);

    size_t start_pos = reader.tell();
    char ch;

    if (!reader.peekChar(ch)) {
        return false;
    }

    double mantissa = 0.0;
    int exponent = 0;
    char sign = '+';
    char exp_sign = '+';
    int read = 0;
    bool leading_decimal_dots = false;

    // Find out what sign we've got
    if (ch == '+' || ch == '-') {
        sign = ch;
        reader.skipBytes(1);
        if (!reader.peekChar(ch)) return false;
        if (ch == '.') {
            leading_decimal_dots = true;
        }
    } else if (IS_DIGIT(ch)) {
        // Pass through
    } else if (ch == '.') {
        leading_decimal_dots = true;
    } else {
        return false;
    }

    // Read the integer part
    if (!leading_decimal_dots) {
        while (reader.peekChar(ch) && IS_DIGIT(ch)) {
            mantissa *= 10.0;
            mantissa += static_cast<int>(ch - '0');
            reader.skipBytes(1);
            read++;
        }

        if (read == 0) return false;
    }

    if (!reader.peekChar(ch)) {
        result = (sign == '+' ? 1.0 : -1.0) * mantissa;
        return true;
    }

    // Read the decimal part
    if (ch == '.') {
        reader.skipBytes(1);
        read = 1;
        while (reader.peekChar(ch) && IS_DIGIT(ch)) {
            const int lut_entries = sizeof(kPow10Inv) / sizeof(kPow10Inv[0]);
            mantissa += static_cast<int>(ch - '0') *
                       (read < lut_entries ? kPow10Inv[read] : customPow(10.0, -read));
            read++;
            reader.skipBytes(1);
        }
    }

    if (!reader.peekChar(ch)) {
        result = (sign == '+' ? 1.0 : -1.0) * mantissa;
        return true;
    }

    // Read the exponent part
    if (ch == 'e' || ch == 'E') {
        reader.skipBytes(1);
        if (!reader.peekChar(ch)) return false;

        if (ch == '+' || ch == '-') {
            exp_sign = ch;
            reader.skipBytes(1);
            if (!reader.peekChar(ch)) return false;
        }

        if (!IS_DIGIT(ch)) return false;

        read = 0;
        while (reader.peekChar(ch) && IS_DIGIT(ch)) {
            if (exponent > (2147483647 / 10)) {  // Overflow check
                return false;
            }
            exponent *= 10;
            exponent += static_cast<int>(ch - '0');
            reader.skipBytes(1);
            read++;
        }
        exponent *= (exp_sign == '+' ? 1 : -1);
        if (read == 0) return false;
    }

    // Assemble result using custom ldexp (only +, -, *, / operations)
    result = (sign == '+' ? 1.0 : -1.0) *
             (exponent ? customLdexp(mantissa * customPow(5.0, exponent), exponent)
                       : mantissa);
    return true;
}

// Helper to parse a float/double
inline bool parseRealNumber(StreamReader& reader, real_t& value) {
    double val;
    if (!tryParseDouble(reader, val)) {
        return false;
    }
    value = static_cast<real_t>(val);
    return true;
}

// Custom integer parsing (avoids std::strtol/atoi)
inline bool parseInteger(StreamReader& reader, int& value) {
    skipSpaces(reader);

    char ch;
    if (!reader.peekChar(ch)) {
        return false;
    }

    bool negative = false;
    if (ch == '-') {
        negative = true;
        reader.skipBytes(1);
        if (!reader.peekChar(ch)) return false;
    } else if (ch == '+') {
        reader.skipBytes(1);
        if (!reader.peekChar(ch)) return false;
    }

    if (!IS_DIGIT(ch)) {
        return false;
    }

    int result = 0;
    while (reader.peekChar(ch) && IS_DIGIT(ch)) {
        // Check for overflow
        if (result > (2147483647 / 10)) {
            return false;
        }
        result = result * 10 + (ch - '0');
        reader.skipBytes(1);
    }

    value = negative ? -result : result;
    return true;
}

// Read word (non-whitespace sequence) - minimizes string allocations
inline bool readWord(StreamReader& reader, std::string& word) {
    word.clear();
    skipSpaces(reader);

    char ch;
    while (reader.peekChar(ch)) {
        if (IS_SPACE(ch) || IS_NEW_LINE(ch)) {
            break;
        }
        word.push_back(ch);
        reader.skipBytes(1);
    }

    return !word.empty();
}

#undef IS_SPACE
#undef IS_DIGIT
#undef IS_NEW_LINE

} // namespace detail

// ObjParser implementation
inline bool ObjParser::parseFloat(StreamReader& reader, real_t& value, ParseState& state, ErrorStack& errors) {
    if (!detail::parseRealNumber(reader, value)) {
        errors.pushError("Failed to parse float", state.current_context);
        return false;
    }
    return true;
}

inline bool ObjParser::parseInt(StreamReader& reader, int& value, ParseState& state, ErrorStack& errors) {
    if (!detail::parseInteger(reader, value)) {
        errors.pushError("Failed to parse integer", state.current_context);
        return false;
    }
    return true;
}

inline int ObjParser::fixIndex(int idx, size_t count, ParseState& state, ErrorStack& errors) {
    if (idx == 0) {
        errors.pushFatal("Index cannot be zero", state.current_context);
        return -1;
    }

    // Convert to 0-based index
    if (idx > 0) {
        idx = idx - 1;
    } else {
        // Negative index is relative to end
        idx = static_cast<int>(count) + idx;
    }

    if (config_.validate_indices) {
        if (idx < 0 || idx >= static_cast<int>(count)) {
            errors.pushFatal("Index out of range", state.current_context);
            return -1;
        }
    }

    return idx;
}

inline bool ObjParser::parseIndex(StreamReader& reader, index_t& idx, ParseState& state, ErrorStack& errors) {
    // Format: v/vt/vn or v//vn or v/vt or v
    idx.vertex_index = -1;
    idx.texcoord_index = -1;
    idx.normal_index = -1;

    int v_idx;
    if (!parseInt(reader, v_idx, state, errors)) {
        return false;
    }
    idx.vertex_index = fixIndex(v_idx, state.vertex_count, state, errors);

    char ch;
    if (!reader.peekChar(ch) || ch != '/') {
        return true;
    }
    reader.skipBytes(1);  // Skip '/'

    // Check for empty texcoord (v//vn case)
    if (reader.peekChar(ch) && ch != '/') {
        int vt_idx;
        if (parseInt(reader, vt_idx, state, errors)) {
            idx.texcoord_index = fixIndex(vt_idx, state.texcoord_count, state, errors);
        }
    }

    if (!reader.peekChar(ch) || ch != '/') {
        return true;
    }
    reader.skipBytes(1);  // Skip '/'

    int vn_idx;
    if (parseInt(reader, vn_idx, state, errors)) {
        idx.normal_index = fixIndex(vn_idx, state.normal_count, state, errors);
    }

    return true;
}

inline bool ObjParser::parseVertex(StreamReader& reader, ParseState& state, ParseResult& result) {
    real_t x, y, z, w = 1.0;
    real_t r = -1.0, g = -1.0, b = -1.0;  // Default: no color

    if (!parseFloat(reader, x, state, result.errors())) return false;
    if (!parseFloat(reader, y, state, result.errors())) return false;
    if (!parseFloat(reader, z, state, result.errors())) return false;

    // Optional w component or vertex colors (r g b)
    detail::skipSpaces(reader);
    char ch;
    if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
        // Try to parse w or first color component
        real_t val;
        if (parseFloat(reader, val, state, result.errors())) {
            // Check if there are more values (colors)
            detail::skipSpaces(reader);
            if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
                // We have more values, so first value is w, next are colors
                w = val;
                if (parseFloat(reader, r, state, result.errors())) {
                    detail::skipSpaces(reader);
                    if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
                        parseFloat(reader, g, state, result.errors());
                        detail::skipSpaces(reader);
                        if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
                            parseFloat(reader, b, state, result.errors());
                        }
                    }
                }
            } else {
                // Only one extra value - it's w
                w = val;
            }
        }
    }

    result.attributes().vertices.push_back(x);
    result.attributes().vertices.push_back(y);
    result.attributes().vertices.push_back(z);

    if (w != 1.0) {
        result.attributes().vertex_weights.push_back(w);
    }

    // Store vertex colors if present
    if (r >= 0.0 && g >= 0.0 && b >= 0.0) {
        result.attributes().colors.push_back(r);
        result.attributes().colors.push_back(g);
        result.attributes().colors.push_back(b);
    } else if (r >= 0.0) {
        // Partial color data - fill with defaults
        result.attributes().colors.push_back(r);
        result.attributes().colors.push_back(g >= 0.0 ? g : 0.0);
        result.attributes().colors.push_back(b >= 0.0 ? b : 0.0);
    }

    state.vertex_count++;
    result.stats().vertices_parsed++;

    return true;
}

inline bool ObjParser::parseNormal(StreamReader& reader, ParseState& state, ParseResult& result) {
    real_t x, y, z;

    if (!parseFloat(reader, x, state, result.errors())) return false;
    if (!parseFloat(reader, y, state, result.errors())) return false;
    if (!parseFloat(reader, z, state, result.errors())) return false;

    result.attributes().normals.push_back(x);
    result.attributes().normals.push_back(y);
    result.attributes().normals.push_back(z);

    state.normal_count++;
    result.stats().normals_parsed++;

    return true;
}

inline bool ObjParser::parseTexCoord(StreamReader& reader, ParseState& state, ParseResult& result) {
    real_t u, v = 0.0, w = 0.0;

    if (!parseFloat(reader, u, state, result.errors())) return false;

    // v is optional
    detail::skipSpaces(reader);
    char ch;
    if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
        parseFloat(reader, v, state, result.errors());

        // w is optional
        detail::skipSpaces(reader);
        if (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
            parseFloat(reader, w, state, result.errors());
        }
    }

    result.attributes().texcoords.push_back(u);
    result.attributes().texcoords.push_back(v);

    if (w != 0.0) {
        result.attributes().texcoord_ws.push_back(w);
    }

    state.texcoord_count++;
    result.stats().texcoords_parsed++;

    return true;
}

inline bool ObjParser::parseLinePrimitive(StreamReader& reader, ParseState& state, ParseResult& result) {
    // Ensure we have a current shape
    if (state.current_shape_index < 0) {
        // Create default shape
        state.current_shape_index = static_cast<int>(result.shapes().size());
        result.shapes().push_back(shape_t());
        result.shapes().back().name = "default";
    }

    shape_t& shape = result.shapes()[state.current_shape_index];
    std::vector<index_t> line_indices;

    detail::skipSpaces(reader);
    char ch;

    // Parse all vertex indices on this line
    while (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
        index_t idx;
        if (!parseIndex(reader, idx, state, result.errors())) {
            result.errors().pushWarning("Failed to parse line index", state.current_context);
            reader.skipLine();
            return false;
        }

        line_indices.push_back(idx);
        detail::skipSpaces(reader);
    }

    if (line_indices.size() < 2) {
        result.errors().pushWarning("Line primitive requires at least 2 vertices", state.current_context);
        return false;
    }

    // Add line indices to shape
    for (const auto& idx : line_indices) {
        shape.lines.indices.push_back(idx);
    }
    shape.lines.num_line_vertices.push_back(static_cast<unsigned char>(line_indices.size()));

    return true;
}

inline bool ObjParser::parsePointPrimitive(StreamReader& reader, ParseState& state, ParseResult& result) {
    // Ensure we have a current shape
    if (state.current_shape_index < 0) {
        // Create default shape
        state.current_shape_index = static_cast<int>(result.shapes().size());
        result.shapes().push_back(shape_t());
        result.shapes().back().name = "default";
    }

    shape_t& shape = result.shapes()[state.current_shape_index];

    detail::skipSpaces(reader);
    char ch;

    // Parse all vertex indices on this line
    while (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
        index_t idx;
        if (!parseIndex(reader, idx, state, result.errors())) {
            result.errors().pushWarning("Failed to parse point index", state.current_context);
            reader.skipLine();
            return false;
        }

        shape.points.indices.push_back(idx);
        detail::skipSpaces(reader);
    }

    return true;
}

inline bool ObjParser::parseFace(StreamReader& reader, ParseState& state, ParseResult& result) {
    std::vector<index_t> face_indices;

    detail::skipSpaces(reader);
    char ch;

    // Parse all vertex indices on this line
    while (reader.peekChar(ch) && ch != '\n' && ch != '\r' && ch != '#') {
        index_t idx;
        if (!parseIndex(reader, idx, state, result.errors())) {
            result.errors().pushWarning("Failed to parse face index", state.current_context);
            reader.skipLine();
            return false;
        }

        face_indices.push_back(idx);
        detail::skipSpaces(reader);
    }

    if (face_indices.size() < 3) {
        result.errors().pushError("Face must have at least 3 vertices", state.current_context);
        return false;
    }

    // Ensure we have a current shape
    if (state.current_shape_index < 0 || state.current_shape_index >= static_cast<int>(result.shapes().size())) {
        shape_t shape;
        shape.name = state.current_object.empty() ? "default" : state.current_object;
        result.shapes().push_back(shape);
        state.current_shape_index = static_cast<int>(result.shapes().size()) - 1;
    }

    shape_t& current_shape = result.shapes()[state.current_shape_index];

    if (config_.triangulate && face_indices.size() > 3) {
        // Simple fan triangulation
        for (size_t i = 2; i < face_indices.size(); ++i) {
            current_shape.mesh.indices.push_back(face_indices[0]);
            current_shape.mesh.indices.push_back(face_indices[i - 1]);
            current_shape.mesh.indices.push_back(face_indices[i]);
            current_shape.mesh.num_face_vertices.push_back(3);
            current_shape.mesh.material_ids.push_back(state.current_material_id);
            current_shape.mesh.smoothing_group_ids.push_back(state.current_smoothing_group_id);
            result.stats().triangles_generated++;
        }
    } else {
        // Keep as-is
        for (const auto& idx : face_indices) {
            current_shape.mesh.indices.push_back(idx);
        }
        current_shape.mesh.num_face_vertices.push_back(static_cast<unsigned int>(face_indices.size()));
        current_shape.mesh.material_ids.push_back(state.current_material_id);
        current_shape.mesh.smoothing_group_ids.push_back(state.current_smoothing_group_id);
    }

    result.stats().faces_parsed++;

    return true;
}

inline bool ObjParser::parseUsemtl(StreamReader& reader, ParseState& state, ParseResult& result) {
    std::string material_name;
    if (!detail::readWord(reader, material_name)) {
        result.errors().pushError("Failed to parse material name", state.current_context);
        return false;
    }

    // Find material by name
    state.current_material_id = -1;
    for (size_t i = 0; i < result.materials().size(); ++i) {
        if (result.materials()[i].name == material_name) {
            state.current_material_id = static_cast<int>(i);
            break;
        }
    }

    if (state.current_material_id == -1) {
        result.errors().pushWarning("Material not found: " + material_name, state.current_context);
    }

    return true;
}

inline bool ObjParser::parseMtllib(StreamReader& reader, ParseState& state, ParseResult& result) {
    std::string mtl_filename;
    if (!detail::readWord(reader, mtl_filename)) {
        result.errors().pushError("Failed to parse material library name", state.current_context);
        return false;
    }

    // Construct full path to material file
    std::string mtl_path;
    if (!config_.mtl_search_path.empty()) {
        mtl_path = config_.mtl_search_path;
        if (mtl_path.back() != '/' && mtl_path.back() != '\\') {
            mtl_path += '/';
        }
    }
    mtl_path += mtl_filename;

    // Parse material file
    return parseMaterialFile(mtl_path, state, result);
}

inline bool ObjParser::parseGroup(StreamReader& reader, ParseState& state, ParseResult& result) {
    state.current_groups.clear();

    std::string group_name;
    while (detail::readWord(reader, group_name)) {
        state.current_groups.push_back(group_name);
    }

    if (state.current_groups.empty()) {
        state.current_groups.push_back("default");
    }

    // Create new shape for this group
    // Join all group names with spaces (e.g., "g front cube" becomes "front cube")
    shape_t shape;
    for (size_t i = 0; i < state.current_groups.size(); ++i) {
        if (i > 0) shape.name += " ";
        shape.name += state.current_groups[i];
    }
    result.shapes().push_back(shape);
    state.current_shape_index = static_cast<int>(result.shapes().size()) - 1;

    return true;
}

inline bool ObjParser::parseObject(StreamReader& reader, ParseState& state, ParseResult& result) {
    std::string object_name;
    if (!detail::readWord(reader, object_name)) {
        object_name = "default";
    }

    state.current_object = object_name;

    // Create new shape for this object
    shape_t shape;
    shape.name = object_name;
    result.shapes().push_back(shape);
    state.current_shape_index = static_cast<int>(result.shapes().size()) - 1;

    return true;
}

inline bool ObjParser::parseLine(StreamReader& reader, ParseState& state, ParseResult& result) {
    std::string line;
    if (!reader.readLine(line, config_.max_line_length)) {
        return false;
    }

    state.line_number++;
    state.current_context.line_number = state.line_number;
    state.current_context.line_content = line;

    // Create a reader for this line
    StreamReader line_reader(line.data(), line.size());

    // Skip leading whitespace
    detail::skipSpaces(line_reader);

    char ch;
    if (!line_reader.peekChar(ch)) {
        return true;  // Empty line
    }

    // Skip comments
    if (ch == '#') {
        return true;
    }

    // Parse command
    std::string cmd;
    if (!detail::readWord(line_reader, cmd)) {
        return true;
    }

    if (cmd == "v") {
        return parseVertex(line_reader, state, result);
    } else if (cmd == "vn") {
        return parseNormal(line_reader, state, result);
    } else if (cmd == "vt") {
        return parseTexCoord(line_reader, state, result);
    } else if (cmd == "f") {
        return parseFace(line_reader, state, result);
    } else if (cmd == "l") {
        return parseLinePrimitive(line_reader, state, result);
    } else if (cmd == "p") {
        return parsePointPrimitive(line_reader, state, result);
    } else if (cmd == "usemtl") {
        return parseUsemtl(line_reader, state, result);
    } else if (cmd == "mtllib") {
        return parseMtllib(line_reader, state, result);
    } else if (cmd == "g") {
        return parseGroup(line_reader, state, result);
    } else if (cmd == "o") {
        return parseObject(line_reader, state, result);
    } else if (cmd == "s") {
        // Smoothing group
        std::string sg_str;
        detail::skipSpaces(line_reader);
        if (detail::readWord(line_reader, sg_str)) {
            if (sg_str == "off") {
                state.current_smoothing_group_id = 0;  // off
            } else {
                // Parse as integer using strtol since readWord already consumed it
                char* endptr;
                long val = strtol(sg_str.c_str(), &endptr, 10);
                if (*endptr == '\0' && val >= 0) {
                    state.current_smoothing_group_id = static_cast<unsigned int>(val);
                } else {
                    state.current_smoothing_group_id = 0;
                }
            }
        }
        return true;
    } else {
        // Unknown command - just skip
        result.errors().pushInfo("Unknown command: " + cmd, state.current_context);
        return true;
    }
}

inline ParseResult ObjParser::parse(StreamReader& reader) {
    ParseResult result;
    ParseState state;

    result.stats().bytes_processed = reader.size();

    while (!reader.eof()) {
        if (!parseLine(reader, state, result)) {
            if (config_.strict_mode) {
                result.errors().pushFatal("Parse error in strict mode", state.current_context);
                break;
            }
        }
    }

    return result;
}

inline ParseResult ObjParser::parseFromMemory(const void* data, size_t size) {
    StreamReader reader(data, size);
    return parse(reader);
}

inline ParseResult ObjParser::parseFromString(const std::string& content) {
    return parseFromMemory(content.data(), content.size());
}

inline bool ObjParser::parseStreaming(StreamReader& reader, StreamingCallbacks& callbacks) {
    ParseState state;
    ParseResult result;  // Temporary for errors

    while (!reader.eof()) {
        if (callbacks.shouldContinue && !callbacks.shouldContinue(callbacks.user_data)) {
            return false;
        }

        // Parse line and trigger callbacks
        // This is a simplified version - full implementation would call callbacks
        if (!parseLine(reader, state, result)) {
            return false;
        }
    }

    return true;
}

// ============================================================================
// Material parsing implementation
// ============================================================================

inline bool ObjParser::parseTextureOption(StreamReader& reader, texture_option_t& texopt, ParseState& state, ErrorStack& errors) {
    // Initialize with defaults
    texopt.type = TEXTURE_TYPE_NONE;
    texopt.sharpness = 1.0;
    texopt.brightness = 0.0;
    texopt.contrast = 1.0;
    texopt.origin_offset[0] = texopt.origin_offset[1] = texopt.origin_offset[2] = 0.0;
    texopt.scale[0] = texopt.scale[1] = texopt.scale[2] = 1.0;
    texopt.turbulence[0] = texopt.turbulence[1] = texopt.turbulence[2] = 0.0;
    texopt.texture_resolution = -1;
    texopt.clamp = false;
    texopt.imfchan = 'm';
    texopt.blendu = true;
    texopt.blendv = true;
    texopt.bump_multiplier = 1.0;

    char ch;
    while (reader.peekChar(ch) && ch == '-') {
        reader.skipBytes(1);  // Skip '-'

        std::string option;
        if (!detail::readWord(reader, option)) {
            break;
        }

        if (option == "blendu") {
            std::string value;
            if (detail::readWord(reader, value)) {
                texopt.blendu = (value == "on");
            }
        } else if (option == "blendv") {
            std::string value;
            if (detail::readWord(reader, value)) {
                texopt.blendv = (value == "on");
            }
        } else if (option == "clamp") {
            std::string value;
            if (detail::readWord(reader, value)) {
                texopt.clamp = (value == "on");
            }
        } else if (option == "boost") {
            parseFloat(reader, texopt.sharpness, state, errors);
        } else if (option == "mm") {
            parseFloat(reader, texopt.brightness, state, errors);
            parseFloat(reader, texopt.contrast, state, errors);
        } else if (option == "o") {
            parseFloat(reader, texopt.origin_offset[0], state, errors);
            detail::skipSpaces(reader);
            if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                parseFloat(reader, texopt.origin_offset[1], state, errors);
                detail::skipSpaces(reader);
                if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                    parseFloat(reader, texopt.origin_offset[2], state, errors);
                }
            }
        } else if (option == "s") {
            parseFloat(reader, texopt.scale[0], state, errors);
            detail::skipSpaces(reader);
            if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                parseFloat(reader, texopt.scale[1], state, errors);
                detail::skipSpaces(reader);
                if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                    parseFloat(reader, texopt.scale[2], state, errors);
                }
            }
        } else if (option == "t") {
            parseFloat(reader, texopt.turbulence[0], state, errors);
            detail::skipSpaces(reader);
            if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                parseFloat(reader, texopt.turbulence[1], state, errors);
                detail::skipSpaces(reader);
                if (reader.peekChar(ch) && ch != '-' && ch != '\n' && ch != '\r') {
                    parseFloat(reader, texopt.turbulence[2], state, errors);
                }
            }
        } else if (option == "bm") {
            parseFloat(reader, texopt.bump_multiplier, state, errors);
        } else if (option == "imfchan") {
            std::string channel;
            if (detail::readWord(reader, channel) && !channel.empty()) {
                texopt.imfchan = channel[0];
            }
        } else if (option == "type") {
            std::string type;
            if (detail::readWord(reader, type)) {
                if (type == "sphere") {
                    texopt.type = TEXTURE_TYPE_SPHERE;
                } else if (type == "cube_top") {
                    texopt.type = TEXTURE_TYPE_CUBE_TOP;
                } else if (type == "cube_bottom") {
                    texopt.type = TEXTURE_TYPE_CUBE_BOTTOM;
                } else if (type == "cube_front") {
                    texopt.type = TEXTURE_TYPE_CUBE_FRONT;
                } else if (type == "cube_back") {
                    texopt.type = TEXTURE_TYPE_CUBE_BACK;
                } else if (type == "cube_left") {
                    texopt.type = TEXTURE_TYPE_CUBE_LEFT;
                } else if (type == "cube_right") {
                    texopt.type = TEXTURE_TYPE_CUBE_RIGHT;
                }
            }
        } else if (option == "colorspace") {
            detail::readWord(reader, texopt.colorspace);
        } else if (option == "texres") {
            int texres;
            if (parseInt(reader, texres, state, errors)) {
                texopt.texture_resolution = texres;
            }
        } else {
            // Unknown option, skip
            std::string dummy;
            detail::readWord(reader, dummy);
        }

        detail::skipSpaces(reader);
    }

    return true;
}

inline bool ObjParser::parseMaterialLine(const std::string& cmd, StreamReader& reader, material_t& current_mat, ParseState& state, ParseResult& result) {
    if (cmd == "newmtl") {
        // This shouldn't happen in parseMaterialLine, handled by caller
        return true;
    } else if (cmd == "Ka") {
        // Ambient
        parseFloat(reader, current_mat.ambient[0], state, result.errors());
        parseFloat(reader, current_mat.ambient[1], state, result.errors());
        parseFloat(reader, current_mat.ambient[2], state, result.errors());
    } else if (cmd == "Kd") {
        // Diffuse
        parseFloat(reader, current_mat.diffuse[0], state, result.errors());
        parseFloat(reader, current_mat.diffuse[1], state, result.errors());
        parseFloat(reader, current_mat.diffuse[2], state, result.errors());
        current_mat.pad2 = 1;  // Mark that Kd was explicitly set
    } else if (cmd == "Ks") {
        // Specular
        parseFloat(reader, current_mat.specular[0], state, result.errors());
        parseFloat(reader, current_mat.specular[1], state, result.errors());
        parseFloat(reader, current_mat.specular[2], state, result.errors());
    } else if (cmd == "Kt" || cmd == "Tf") {
        // Transmittance (Kt or Tf)
        parseFloat(reader, current_mat.transmittance[0], state, result.errors());
        parseFloat(reader, current_mat.transmittance[1], state, result.errors());
        parseFloat(reader, current_mat.transmittance[2], state, result.errors());
    } else if (cmd == "Ke") {
        // Emission
        parseFloat(reader, current_mat.emission[0], state, result.errors());
        parseFloat(reader, current_mat.emission[1], state, result.errors());
        parseFloat(reader, current_mat.emission[2], state, result.errors());
    } else if (cmd == "Ns") {
        // Shininess
        parseFloat(reader, current_mat.shininess, state, result.errors());
    } else if (cmd == "Ni") {
        // Index of refraction
        parseFloat(reader, current_mat.ior, state, result.errors());
    } else if (cmd == "d") {
        // Dissolve (opacity)
        // Note: 'd' always wins over 'Tr' - once set, mark it so Tr is ignored
        real_t d;
        if (parseFloat(reader, d, state, result.errors())) {
            current_mat.dissolve = d;
            current_mat.pad0 = 1;  // Use pad0 as flag to indicate 'd' was seen
        }
    } else if (cmd == "Tr") {
        // Transparency (inverse of dissolve)
        // Ignore if 'd' was already specified (pad0 != 0)
        if (current_mat.pad0 == 0) {
            real_t tr;
            if (parseFloat(reader, tr, state, result.errors())) {
                current_mat.dissolve = 1.0 - tr;  // Tr is inverse of d
            }
        } else {
            // Skip the value but don't use it
            real_t dummy;
            parseFloat(reader, dummy, state, result.errors());
        }
    } else if (cmd == "illum") {
        // Illumination model
        parseInt(reader, current_mat.illum, state, result.errors());
    } else if (cmd == "map_Ka") {
        // Ambient texture
        parseTextureOption(reader, current_mat.ambient_texopt, state, result.errors());
        detail::readWord(reader, current_mat.ambient_texname);
    } else if (cmd == "map_Kd") {
        // Diffuse texture
        parseTextureOption(reader, current_mat.diffuse_texopt, state, result.errors());
        detail::readWord(reader, current_mat.diffuse_texname);
        // Set decent diffuse default if Kd wasn't explicitly set
        if (current_mat.pad2 == 0) {
            current_mat.diffuse[0] = 0.6f;
            current_mat.diffuse[1] = 0.6f;
            current_mat.diffuse[2] = 0.6f;
        }
    } else if (cmd == "map_Ks") {
        // Specular texture
        parseTextureOption(reader, current_mat.specular_texopt, state, result.errors());
        detail::readWord(reader, current_mat.specular_texname);
    } else if (cmd == "map_Ns") {
        // Specular highlight texture
        parseTextureOption(reader, current_mat.specular_highlight_texopt, state, result.errors());
        detail::readWord(reader, current_mat.specular_highlight_texname);
    } else if (cmd == "map_d") {
        // Alpha texture
        parseTextureOption(reader, current_mat.alpha_texopt, state, result.errors());
        detail::readWord(reader, current_mat.alpha_texname);
    } else if (cmd == "map_bump" || cmd == "map_Bump" || cmd == "bump") {
        // Bump texture
        parseTextureOption(reader, current_mat.bump_texopt, state, result.errors());
        detail::readWord(reader, current_mat.bump_texname);
    } else if (cmd == "disp") {
        // Displacement texture
        parseTextureOption(reader, current_mat.displacement_texopt, state, result.errors());
        detail::readWord(reader, current_mat.displacement_texname);
    } else if (cmd == "refl") {
        // Reflection texture
        parseTextureOption(reader, current_mat.reflection_texopt, state, result.errors());
        detail::readWord(reader, current_mat.reflection_texname);
    } else if (cmd == "Pr") {
        // PBR: Roughness
        parseFloat(reader, current_mat.roughness, state, result.errors());
    } else if (cmd == "Pm") {
        // PBR: Metallic
        parseFloat(reader, current_mat.metallic, state, result.errors());
    } else if (cmd == "Ps") {
        // PBR: Sheen
        parseFloat(reader, current_mat.sheen, state, result.errors());
    } else if (cmd == "Pc") {
        // PBR: Clearcoat thickness
        parseFloat(reader, current_mat.clearcoat_thickness, state, result.errors());
    } else if (cmd == "Pcr") {
        // PBR: Clearcoat roughness
        parseFloat(reader, current_mat.clearcoat_roughness, state, result.errors());
    } else if (cmd == "aniso") {
        // PBR: Anisotropy
        parseFloat(reader, current_mat.anisotropy, state, result.errors());
    } else if (cmd == "anisor") {
        // PBR: Anisotropy rotation
        parseFloat(reader, current_mat.anisotropy_rotation, state, result.errors());
    } else if (cmd == "map_Pr") {
        // PBR: Roughness texture
        parseTextureOption(reader, current_mat.roughness_texopt, state, result.errors());
        detail::readWord(reader, current_mat.roughness_texname);
    } else if (cmd == "map_Pm") {
        // PBR: Metallic texture
        parseTextureOption(reader, current_mat.metallic_texopt, state, result.errors());
        detail::readWord(reader, current_mat.metallic_texname);
    } else if (cmd == "map_Ps") {
        // PBR: Sheen texture
        parseTextureOption(reader, current_mat.sheen_texopt, state, result.errors());
        detail::readWord(reader, current_mat.sheen_texname);
    } else if (cmd == "map_Ke") {
        // PBR: Emissive texture
        parseTextureOption(reader, current_mat.emissive_texopt, state, result.errors());
        detail::readWord(reader, current_mat.emissive_texname);
    } else if (cmd == "norm") {
        // PBR: Normal map
        parseTextureOption(reader, current_mat.normal_texopt, state, result.errors());
        detail::readWord(reader, current_mat.normal_texname);
    } else {
        // Unknown parameter - store as custom
        std::string value;
        detail::readWord(reader, value);
        current_mat.unknown_parameter[cmd] = value;
    }

    return true;
}

inline bool ObjParser::parseMaterialFile(const std::string& filepath, ParseState& state, ParseResult& result) {
    // Use file callback if provided
    if (!config_.file_callbacks.read_fn) {
        ErrorContext ctx = state.current_context;
        ctx.file_name = filepath;
        result.errors().pushWarning("No file read callback provided for: " + filepath, ctx);
        return false;
    }

    // Call user's file read callback
    size_t file_size = 0;
    const char* file_data = config_.file_callbacks.read_fn(
        filepath.c_str(), &file_size, config_.file_callbacks.user_data);

    if (!file_data || file_size == 0) {
        ErrorContext ctx = state.current_context;
        ctx.file_name = filepath;
        result.errors().pushWarning("Failed to read material file: " + filepath, ctx);
        return false;
    }

    // Create reader from file data
    StreamReader mtl_reader(file_data, file_size);

    // Save current context
    ErrorContext saved_context = state.current_context;
    size_t saved_line_number = state.line_number;

    // Reset for material file
    state.current_context.file_name = filepath;
    state.line_number = 0;

    material_t current_mat;
    bool has_current_mat = false;

    while (!mtl_reader.eof()) {
        std::string line;
        if (!mtl_reader.readLine(line, config_.max_line_length)) {
            break;
        }

        state.line_number++;
        state.current_context.line_number = state.line_number;
        state.current_context.line_content = line;

        // Create reader for this line
        StreamReader line_reader(line.data(), line.size());
        detail::skipSpaces(line_reader);

        char ch;
        if (!line_reader.peekChar(ch)) {
            continue;  // Empty line
        }

        if (ch == '#') {
            continue;  // Comment
        }

        std::string cmd;
        if (!detail::readWord(line_reader, cmd)) {
            continue;
        }

        if (cmd == "newmtl") {
            // Save previous material if any
            if (has_current_mat) {
                result.materials().push_back(current_mat);
                result.stats().materials_loaded++;
            }

            // Start new material
            current_mat = material_t();
            if (!detail::readWord(line_reader, current_mat.name)) {
                current_mat.name = "default";
            }
            has_current_mat = true;
        } else if (has_current_mat) {
            // Parse material property
            detail::skipSpaces(line_reader);
            parseMaterialLine(cmd, line_reader, current_mat, state, result);
        }
    }

    // Save last material
    if (has_current_mat) {
        result.materials().push_back(current_mat);
        result.stats().materials_loaded++;
    }

    // Restore context
    state.current_context = saved_context;
    state.line_number = saved_line_number;

    // Free file data using callback
    if (config_.file_callbacks.free_fn) {
        config_.file_callbacks.free_fn(file_data, config_.file_callbacks.user_data);
    }

    return true;
}

// ============================================================================
// Factory functions
// ============================================================================

inline auto CreateStreamReaderFromMemory(const void* data, size_t size)
    -> std::unique_ptr<StreamReader> {
    return std::make_unique<StreamReader>(data, size);
}

inline auto CreateStreamReaderFromString(const std::string& content)
    -> std::unique_ptr<StreamReader> {
    return std::make_unique<StreamReader>(content.data(), content.size());
}

// ============================================================================
// Example file callback implementations (user can provide their own)
// ============================================================================

// Example: POSIX-style file reading (not included by default, user provides)
/*
#include <cstdio>
#include <cstdlib>

const char* ExampleFileRead(const char* filepath, size_t* out_size, void* user_data) {
    FILE* fp = fopen(filepath, "rb");
    if (!fp) return nullptr;

    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    char* buffer = (char*)malloc(size);
    if (!buffer) {
        fclose(fp);
        return nullptr;
    }

    size_t read = fread(buffer, 1, size, fp);
    fclose(fp);

    *out_size = read;
    return buffer;
}

void ExampleFileFree(const char* data, void* user_data) {
    free((void*)data);
}

// Usage:
ParserConfig config;
config.file_callbacks.read_fn = ExampleFileRead;
config.file_callbacks.free_fn = ExampleFileFree;
config.file_callbacks.user_data = nullptr;
*/

} // namespace v3
} // namespace tinyobj

#endif // TINYOBJ_V3_HH_
