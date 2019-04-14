from distutils.core import setup, Extension


# `../tiny_obj_loader.cc` contains implementation of tiny_obj_loader.
m = Extension('tinyobj',
              sources = ['bindings.cc', '../tiny_obj_loader.cc'],
              extra_compile_args=['-std=c++11'],
              include_dirs = ['../', '../pybind11/include']
              )


setup (name = 'tinyobj',
       version = '0.1',
       description = 'Python module for tinyobjloader',
       ext_modules = [m])


