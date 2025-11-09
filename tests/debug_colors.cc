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
    return buffer;
}

void PosixFileFree(const char* data, void* user_data) {
    (void)user_data;
    free((void*)data);
}

int main() {
    size_t obj_size;
    const char* obj_data = PosixFileRead("../models/cube-vertexcol.obj", &obj_size, nullptr);
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
    const auto& attrib = result.attributes();
    printf("Colors size: %zu (expected 24 for 8 vertices)\n", attrib.colors.size());
    printf("Vertices: %zu\n", attrib.vertices.size() / 3);

    // Print vertex 0
    printf("\nVertex 0 colors: [%f, %f, %f] (expected [0, 0, 0])\n",
           attrib.colors[0], attrib.colors[1], attrib.colors[2]);

    // Print vertex 1
    printf("Vertex 1 colors: [%f, %f, %f] (expected [0, 0, 1])\n",
           attrib.colors[3], attrib.colors[4], attrib.colors[5]);

    // Print vertex 7
    printf("Vertex 7 colors: [%f, %f, %f] (expected [1, 1, 1])\n",
           attrib.colors[21], attrib.colors[22], attrib.colors[23]);

    return 0;
}
