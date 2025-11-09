# TinyObjLoader v3 - File Callback API

## Overview

✅ **std::ifstream REMOVED** - TinyObjLoader v3 now uses a **callback-based file I/O system**.

Users provide their own file reading implementation, giving complete control over:
- File system access (POSIX, Win32, custom VFS, etc.)
- Memory management (malloc, custom allocators, memory pools)
- Async/threaded loading
- Encrypted/compressed files
- Network file systems

## API Design

### File Callback Types

```cpp
// Read callback - load file into memory
typedef const char* (*FileReadCallback)(
    const char* filepath,  // Path to file
    size_t* out_size,      // OUTPUT: size of file data
    void* user_data        // User context
);

// Free callback - release file memory
typedef void (*FileFreeCallback)(
    const char* data,      // Data returned by FileReadCallback
    void* user_data        // User context
);
```

### FileCallbacks Structure

```cpp
struct FileCallbacks {
    FileReadCallback read_fn;
    FileFreeCallback free_fn;
    void* user_data;
};
```

### Configuration

```cpp
struct ParserConfig {
    // ... other settings ...

    // File I/O callbacks (required for .mtl loading)
    FileCallbacks file_callbacks;
};
```

## Usage Examples

### Example 1: POSIX File I/O

```cpp
#include <cstdio>
#include <cstdlib>

const char* PosixFileRead(const char* filepath, size_t* out_size, void* user_data) {
    FILE* fp = fopen(filepath, "rb");
    if (!fp) {
        *out_size = 0;
        return nullptr;
    }

    // Get file size
    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    // Allocate buffer
    char* buffer = (char*)malloc(size);
    if (!buffer) {
        fclose(fp);
        *out_size = 0;
        return nullptr;
    }

    // Read file
    size_t bytes_read = fread(buffer, 1, size, fp);
    fclose(fp);

    *out_size = bytes_read;
    return buffer;
}

void PosixFileFree(const char* data, void* user_data) {
    free((void*)data);
}

// Usage:
tinyobj::v3::ParserConfig config;
config.file_callbacks.read_fn = PosixFileRead;
config.file_callbacks.free_fn = PosixFileFree;
config.file_callbacks.user_data = nullptr;

tinyobj::v3::ObjParser parser(config);
auto result = parser.parseFromMemory(obj_data, obj_size);
```

### Example 2: Win32 File I/O

```cpp
#include <windows.h>

const char* Win32FileRead(const char* filepath, size_t* out_size, void* user_data) {
    HANDLE hFile = CreateFileA(filepath, GENERIC_READ, FILE_SHARE_READ,
                                NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (hFile == INVALID_HANDLE_VALUE) {
        *out_size = 0;
        return nullptr;
    }

    DWORD fileSize = GetFileSize(hFile, NULL);
    char* buffer = (char*)malloc(fileSize);
    if (!buffer) {
        CloseHandle(hFile);
        *out_size = 0;
        return nullptr;
    }

    DWORD bytesRead;
    ReadFile(hFile, buffer, fileSize, &bytesRead, NULL);
    CloseHandle(hFile);

    *out_size = bytesRead;
    return buffer;
}

void Win32FileFree(const char* data, void* user_data) {
    free((void*)data);
}
```

### Example 3: Custom Memory Pool

```cpp
struct MemoryPool {
    char* pool;
    size_t used;
    size_t capacity;
};

const char* PoolFileRead(const char* filepath, size_t* out_size, void* user_data) {
    MemoryPool* pool = (MemoryPool*)user_data;

    // Load file with your custom loader
    FILE* fp = fopen(filepath, "rb");
    if (!fp) return nullptr;

    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    // Allocate from pool
    if (pool->used + size > pool->capacity) {
        fclose(fp);
        return nullptr;
    }

    char* buffer = pool->pool + pool->used;
    pool->used += size;

    fread(buffer, 1, size, fp);
    fclose(fp);

    *out_size = size;
    return buffer;
}

void PoolFileFree(const char* data, void* user_data) {
    // Pool memory - no individual free needed
    // Or mark for reuse
}

// Usage:
MemoryPool pool = {/* ... */};
config.file_callbacks.read_fn = PoolFileRead;
config.file_callbacks.free_fn = PoolFileFree;
config.file_callbacks.user_data = &pool;
```

### Example 4: Virtual File System (Game Engine)

```cpp
// Game engine with virtual file system
struct VFS {
    std::map<std::string, std::vector<char>> files;
};

const char* VFSFileRead(const char* filepath, size_t* out_size, void* user_data) {
    VFS* vfs = (VFS*)user_data;

    auto it = vfs->files.find(filepath);
    if (it == vfs->files.end()) {
        *out_size = 0;
        return nullptr;
    }

    // Return pointer to internal buffer
    // Note: Caller must not free this!
    *out_size = it->second.size();
    return it->second.data();
}

void VFSFileFree(const char* data, void* user_data) {
    // VFS owns the data, no free needed
}
```

### Example 5: Encrypted Files

```cpp
const char* EncryptedFileRead(const char* filepath, size_t* out_size, void* user_data) {
    // Read encrypted file
    FILE* fp = fopen(filepath, "rb");
    if (!fp) return nullptr;

    fseek(fp, 0, SEEK_END);
    long encrypted_size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    char* encrypted_data = (char*)malloc(encrypted_size);
    fread(encrypted_data, 1, encrypted_size, fp);
    fclose(fp);

    // Decrypt in-place or to new buffer
    DecryptAES(encrypted_data, encrypted_size);

    *out_size = encrypted_size;  // Or decrypted size
    return encrypted_data;
}
```

### Example 6: Async/Threaded Loading

```cpp
struct AsyncContext {
    std::mutex mutex;
    std::condition_variable cv;
    std::map<std::string, std::vector<char>> loaded_files;
};

const char* AsyncFileRead(const char* filepath, size_t* out_size, void* user_data) {
    AsyncContext* ctx = (AsyncContext*)user_data;

    std::unique_lock<std::mutex> lock(ctx->mutex);

    // Wait for async load to complete
    while (ctx->loaded_files.find(filepath) == ctx->loaded_files.end()) {
        ctx->cv.wait(lock);
    }

    auto& file_data = ctx->loaded_files[filepath];
    *out_size = file_data.size();
    return file_data.data();
}
```

### Example 7: Network File System

```cpp
const char* NetworkFileRead(const char* filepath, size_t* out_size, void* user_data) {
    const char* base_url = (const char*)user_data;

    // Construct URL: base_url + filepath
    std::string url = std::string(base_url) + "/" + filepath;

    // HTTP GET request
    char* buffer = nullptr;
    size_t size = HTTPGet(url.c_str(), &buffer);

    *out_size = size;
    return buffer;
}
```

## Complete Usage Example

```cpp
#include "tinyobj_v3.hh"
#include <cstdio>
#include <cstdlib>

// Simple POSIX file callbacks
const char* ReadFile(const char* path, size_t* size, void* user_data) {
    FILE* fp = fopen(path, "rb");
    if (!fp) return nullptr;

    fseek(fp, 0, SEEK_END);
    *size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    char* buf = (char*)malloc(*size);
    fread(buf, 1, *size, fp);
    fclose(fp);
    return buf;
}

void FreeFile(const char* data, void* user_data) {
    free((void*)data);
}

int main() {
    // Load .obj file yourself
    size_t obj_size;
    const char* obj_data = ReadFile("model.obj", &obj_size, nullptr);

    // Configure parser with file callbacks for .mtl
    tinyobj::v3::ParserConfig config;
    config.file_callbacks.read_fn = ReadFile;
    config.file_callbacks.free_fn = FreeFile;
    config.file_callbacks.user_data = nullptr;
    config.mtl_search_path = "./materials/";

    // Parse OBJ
    tinyobj::v3::ObjParser parser(config);
    auto result = parser.parseFromMemory(obj_data, obj_size);

    // Free OBJ data
    FreeFile(obj_data, nullptr);

    // Check results
    if (!result.success()) {
        printf("Parse errors:\n%s\n", result.errors().formatErrors().c_str());
        return 1;
    }

    printf("Loaded %zu vertices\n", result.stats().vertices_parsed);
    printf("Loaded %zu materials\n", result.stats().materials_loaded);

    // Use data
    for (const auto& shape : result.shapes()) {
        // Process shape
    }

    return 0;
}
```

## API Changes from v2

### Before (v2):
```cpp
// v2 used std::ifstream internally
tinyobj::ObjReader reader;
reader.ParseFromFile("model.obj");  // Automatic file I/O
```

### After (v3):
```cpp
// v3 requires user to load file + provide callbacks
const char* data = LoadFileYourWay("model.obj", &size);

tinyobj::v3::ParserConfig config;
config.file_callbacks.read_fn = YourReadCallback;
config.file_callbacks.free_fn = YourFreeCallback;

tinyobj::v3::ObjParser parser(config);
auto result = parser.parseFromMemory(data, size);

FreeFileYourWay(data);
```

## Benefits

1. ✅ **No std::ifstream dependency**
2. ✅ **Platform independent** (POSIX, Win32, embedded, custom)
3. ✅ **Full memory control** (malloc, custom allocators, pools)
4. ✅ **VFS support** (game engines, archives, encrypted files)
5. ✅ **Async loading** (background threads, streaming)
6. ✅ **Network files** (HTTP, FTP, custom protocols)
7. ✅ **Smaller binary** (no iostream template bloat)
8. ✅ **Embedded friendly** (no FILE* or OS dependencies required)

## Callback Contract

### FileReadCallback Requirements:
- **MUST** return valid pointer to file data, or `nullptr` on failure
- **MUST** set `*out_size` to size of file data in bytes
- Data **MUST** remain valid until `FileFreeCallback` is called
- Data **MUST** be readable for at least `*out_size` bytes
- Return value can be stack/heap/mmap/whatever, as long as it's valid

### FileFreeCallback Requirements:
- **MUST** free/release resources allocated by `FileReadCallback`
- Called exactly once for each successful `FileReadCallback`
- Can be no-op if data doesn't need freeing (e.g., mmap, static buffer)

## Thread Safety

File callbacks are called **synchronously** during parsing:
- `FileReadCallback` is called when `mtllib` is encountered
- `FileFreeCallback` is called after material parsing completes
- No concurrent calls to callbacks from v3 parser

User is responsible for thread safety if:
- Multiple parsers run in different threads
- Callbacks access shared state (VFS, memory pools, etc.)

## Error Handling

If `FileReadCallback` returns `nullptr`:
- Parser continues (MTL loading is optional)
- Warning added to error stack
- Materials will be missing, but parsing continues

If callbacks are not provided:
- Warning added when `mtllib` is encountered
- MTL files are not loaded
- OBJ parsing continues normally

## Migration from v2

Replace:
```cpp
// v2: Automatic file loading
reader.ParseFromFile("model.obj");
```

With:
```cpp
// v3: Manual file loading
size_t size;
const char* data = YourFileLoad("model.obj", &size);
result = parser.parseFromMemory(data, size);
YourFileFree(data);
```

And configure MTL callbacks:
```cpp
config.file_callbacks.read_fn = YourReadCallback;
config.file_callbacks.free_fn = YourFreeCallback;
```

## Conclusion

The callback-based file I/O system provides **maximum flexibility** while maintaining **zero STL file I/O dependencies**. Users have complete control over how files are loaded, making v3 suitable for any environment from embedded systems to modern game engines.
