#include "../tinyobj_v3.hh"
#include <cstdio>
#include <cstdlib>

const char* PosixFileRead(const char* filepath, size_t* out_size, void* user_data) {
    (void)user_data;
    FILE* fp = fopen(filepath, "rb");
    if (!fp) {
        printf("Failed to open: %s\n", filepath);
        *out_size = 0;
        return nullptr;
    }

    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    char* buffer = (char*)malloc(size);
    if (!buffer) {
        fclose(fp);
        *out_size = 0;
        return nullptr;
    }

    size_t bytes_read = fread(buffer, 1, size, fp);
    fclose(fp);

    *out_size = bytes_read;
    printf("Read file: %s (%zu bytes)\n", filepath, bytes_read);
    return buffer;
}

void PosixFileFree(const char* data, void* user_data) {
    (void)user_data;
    free((void*)data);
}

int main() {
    size_t obj_size;
    const char* obj_data = PosixFileRead("../models/tr-and-d-issue-43.obj", &obj_size, nullptr);
    if (!obj_data) {
        printf("Failed to load OBJ\n");
        return 1;
    }

    tinyobj::v3::ParserConfig config;
    config.file_callbacks.read_fn = PosixFileRead;
    config.file_callbacks.free_fn = PosixFileFree;
    config.mtl_search_path = "../models/";

    tinyobj::v3::ObjParser parser(config);
    auto result = parser.parseFromMemory(obj_data, obj_size);

    PosixFileFree(obj_data, nullptr);

    if (!result.success()) {
        printf("Parse failed!\n");
        printf("Errors: %s\n", result.errors().formatErrors().c_str());
        return 1;
    }

    printf("Parse succeeded!\n");
    printf("Materials loaded: %zu\n", result.materials().size());

    for (size_t i = 0; i < result.materials().size(); i++) {
        const auto& mat = result.materials()[i];
        printf("Material[%zu]: name='%s', dissolve=%f\n", i, mat.name.c_str(), mat.dissolve);
    }

    return 0;
}
