#!/usr/bin/env python3
"""
Setup script for TinyObjLoader v3 Python bindings

This builds the v3 module separately from the v2 module using:
- Python Stable ABI (abi3) for forward compatibility
- Python 3.10+ minimum requirement
- No dependency on Python.h at build time (uses manual ABI definitions)
"""

import sys
import os
from setuptools import setup, Extension

# Read version
try:
    from python import _version
    __version__ = _version.__version__
except:
    __version__ = "3.0.0"

with open("README.md", "r", encoding="utf8") as fh:
    long_description = fh.read()

# Compiler and linker flags for stable ABI
extra_compile_args = [
    '-std=c++14',
    '-fno-exceptions',  # v3 doesn't use exceptions
    '-fno-rtti',        # v3 doesn't use RTTI
    '-DPy_LIMITED_API=0x030A0000',  # Python 3.10+
]

extra_link_args = []

# Platform-specific flags
if sys.platform == 'darwin':
    # macOS
    extra_compile_args.extend([
        '-mmacosx-version-min=10.13',
        '-fvisibility=hidden',
    ])
elif sys.platform.startswith('linux'):
    # Linux
    extra_compile_args.extend([
        '-fvisibility=hidden',
    ])
    extra_link_args.extend([
        '-Wl,--exclude-libs,ALL',
    ])
elif sys.platform == 'win32':
    # Windows MSVC
    if 'MSC' in sys.version:
        extra_compile_args = [
            '/std:c++14',
            '/DPy_LIMITED_API=0x030A0000',
            '/D_CRT_SECURE_NO_WARNINGS',
        ]

# Define the extension module
ext_modules = [
    Extension(
        "tinyobjloader_v3",
        sources=sorted([
            "python/tinyobj_v3_bindings.cc",
            "python/tinyobj_v3_loader.cc",
        ]),
        include_dirs=["."],
        language="c++",
        extra_compile_args=extra_compile_args,
        extra_link_args=extra_link_args,
        py_limited_api=True,  # Enable stable ABI
    ),
]

setup(
    name="tinyobjloader-v3",
    version=__version__,
    author="Syoyo Fujita",
    author_email="syoyo@lighttransport.com",
    url="https://github.com/tinyobjloader/tinyobjloader",
    description="TinyObjLoader v3 - Modern C++14 Wavefront OBJ parser",
    long_description=long_description,
    long_description_content_type='text/markdown',
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Developers",
        "Intended Audience :: Science/Research",
        "Intended Audience :: Manufacturing",
        "Topic :: Artistic Software",
        "Topic :: Multimedia :: Graphics :: 3D Modeling",
        "Topic :: Scientific/Engineering :: Visualization",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
        "Programming Language :: C++",
    ],
    ext_modules=ext_modules,
    python_requires=">=3.10",
    zip_safe=False,
)
