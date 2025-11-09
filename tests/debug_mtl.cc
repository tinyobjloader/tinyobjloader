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
    // Test parsing MTL directly
    const char* mtl_content =
        "# .MTL with PBR extension.\n"
        "newmtl pbr\n"
        "Ka 0 0 0\n"
        "Kd 1 1 1\n"
        "Ks 0 0 0\n"
        "Ke 0.1 0.1 0.1\n"
        "Pr 0.2\n"
        "Pm 0.3\n"
        "Ps 0.4\n"
        "Pc 0.5\n"
        "Pcr 0.6\n"
        "aniso 0.7\n"
        "anisor 0.8\n"
        "map_Pr roughness.tex\n"
        "map_Pm metallic.tex\n";

    printf("MTL content length: %zu\n", strlen(mtl_content));

    tinyobj::v3::ParserConfig config;
    tinyobj::v3::ObjParser parser(config);

    // Parse as MTL directly
    auto result = parser.parseMaterialFromMemory(mtl_content, strlen(mtl_content));

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
        printf("Ka: %f %f %f\n", mat.ambient[0], mat.ambient[1], mat.ambient[2]);
        printf("Kd: %f %f %f\n", mat.diffuse[0], mat.diffuse[1], mat.diffuse[2]);
        printf("Ks: %f %f %f\n", mat.specular[0], mat.specular[1], mat.specular[2]);
        printf("Ke: %f %f %f\n", mat.emission[0], mat.emission[1], mat.emission[2]);
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
