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
    // Load OBJ file
    size_t obj_size;
    const char* obj_data = PosixFileRead("../models/pbr-mat-ext.obj", &obj_size, nullptr);
    if (!obj_data) {
        printf("Failed to load OBJ\n");
        return 1;
    }

    // Configure parser
    tinyobj::v3::ParserConfig config;
    config.triangulate = false;
    config.file_callbacks.read_fn = PosixFileRead;
    config.file_callbacks.free_fn = PosixFileFree;
    config.file_callbacks.user_data = nullptr;
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

    if (result.materials().size() > 0) {
        const auto& mat = result.materials()[0];
        printf("Material name: %s\n", mat.name.c_str());
        printf("Roughness: %f\n", mat.roughness);
        printf("Metallic: %f\n", mat.metallic);
        printf("Sheen: %f\n", mat.sheen);
        printf("Clearcoat: %f\n", mat.clearcoat_thickness);
        printf("Clearcoat roughness: %f\n", mat.clearcoat_roughness);
        printf("Anisotropy: %f\n", mat.anisotropy);
        printf("Anisotropy rotation: %f\n", mat.anisotropy_rotation);
        printf("Roughness tex: %s\n", mat.roughness_texname.c_str());
        printf("Metallic tex: %s\n", mat.metallic_texname.c_str());
    }

    return 0;
}
