from distutils.core import setup, Extension


m = Extension('tinyobjloader',
              sources = ['bindings.cc', '../tiny_obj_loader.cc'],
              extra_compile_args=['-std=c++11'],
              include_dirs = ['../', '../pybind11/include']
              )


setup (name = 'tinyobjloader',
       version = '0.1',
       description = 'Python module for tinyobjloader',
       ext_modules = [m])


