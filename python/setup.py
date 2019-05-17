import setuptools

with open("README.md", "r") as fh:
    long_description= fh.read()

# `tiny_obj_loader.cc` contains implementation of tiny_obj_loader.
m = setuptools.Extension('tinyobjloader',
              sources = ['bindings.cc', 'tiny_obj_loader.cc'],
              extra_compile_args=['-std=c++11'],
              include_dirs = ['../', '../pybind11/include']
              )


setuptools.setup (name = 'tinyobjloader',
       version = '0.1',
       description = 'Python module for tinyobjloader',
       long_description = long_description,
       long_description_content_type = "text/markdown",
       author="Syoyo Fujita",
       author_email="syoyo@lighttransport.com",
       url="https://github.com/syoyo/tinyobjloader",
       classifiers=[
           "License :: OSI Approved :: MIT License",
       ],
       packages=setuptools.find_packages(),
       ext_modules = [m])


