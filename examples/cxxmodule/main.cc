#include <string>
#include <vector>
#include <iostream>

// import std;
import tinyobj;


int main() {
    // Equivalent to doing everything that #include <tiny_obj_loader.h> would do

    const std::string filename = "../../models/cornell_box.obj";
    tinyobj::attrib_t attrib;
    std::vector<tinyobj::shape_t> shapes;
    std::vector<tinyobj::material_t> materials;
    std::string warn, err;
    if (!tinyobj::LoadObj(&attrib, &shapes, &materials, &warn, &err, filename.c_str())) {
        throw std::runtime_error(warn + err);
    }

    std::cout << "shapes.size() = " << shapes.size() << std::endl;
    for (const auto& shape : shapes) {
        std::cout << "shape.mesh.indices.size() = " << shape.mesh.indices.size() << std::endl;
    }

    // ......
}

