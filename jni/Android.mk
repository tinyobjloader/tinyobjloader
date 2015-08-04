# A simple test for the minimal standard C++ library
#

LOCAL_PATH := $(call my-dir)

include $(CLEAR_VARS)
LOCAL_MODULE := tinyobjloader
LOCAL_SRC_FILES := ../tiny_obj_loader.cc ../test.cc

LOCAL_C_INCLUDES := ../

include $(BUILD_EXECUTABLE)
