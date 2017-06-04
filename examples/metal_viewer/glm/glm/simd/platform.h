/// @ref simd
/// @file glm/simd/platform.h

#pragma once

///////////////////////////////////////////////////////////////////////////////////
// Platform

#define GLM_PLATFORM_UNKNOWN		0x00000000
#define GLM_PLATFORM_WINDOWS		0x00010000
#define GLM_PLATFORM_LINUX			0x00020000
#define GLM_PLATFORM_APPLE			0x00040000
//#define GLM_PLATFORM_IOS			0x00080000
#define GLM_PLATFORM_ANDROID		0x00100000
#define GLM_PLATFORM_CHROME_NACL	0x00200000
#define GLM_PLATFORM_UNIX			0x00400000
#define GLM_PLATFORM_QNXNTO			0x00800000
#define GLM_PLATFORM_WINCE			0x01000000
#define GLM_PLATFORM_CYGWIN			0x02000000

#ifdef GLM_FORCE_PLATFORM_UNKNOWN
#	define GLM_PLATFORM GLM_PLATFORM_UNKNOWN
#elif defined(__CYGWIN__)
#	define GLM_PLATFORM GLM_PLATFORM_CYGWIN
#elif defined(__QNXNTO__)
#	define GLM_PLATFORM GLM_PLATFORM_QNXNTO
#elif defined(__APPLE__)
#	define GLM_PLATFORM GLM_PLATFORM_APPLE
#elif defined(WINCE)
#	define GLM_PLATFORM GLM_PLATFORM_WINCE
#elif defined(_WIN32)
#	define GLM_PLATFORM GLM_PLATFORM_WINDOWS
#elif defined(__native_client__)
#	define GLM_PLATFORM GLM_PLATFORM_CHROME_NACL
#elif defined(__ANDROID__)
#	define GLM_PLATFORM GLM_PLATFORM_ANDROID
#elif defined(__linux)
#	define GLM_PLATFORM GLM_PLATFORM_LINUX
#elif defined(__unix)
#	define GLM_PLATFORM GLM_PLATFORM_UNIX
#else
#	define GLM_PLATFORM GLM_PLATFORM_UNKNOWN
#endif//

// Report platform detection
#if(defined(GLM_MESSAGES) && !defined(GLM_MESSAGE_PLATFORM_DISPLAYED))
#	define GLM_MESSAGE_PLATFORM_DISPLAYED
#	if(GLM_PLATFORM & GLM_PLATFORM_QNXNTO)
#		pragma message("GLM: QNX platform detected")
//#	elif(GLM_PLATFORM & GLM_PLATFORM_IOS)
//#		pragma message("GLM: iOS platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_APPLE)
#		pragma message("GLM: Apple platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_WINCE)
#		pragma message("GLM: WinCE platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_WINDOWS)
#		pragma message("GLM: Windows platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_CHROME_NACL)
#		pragma message("GLM: Native Client detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_ANDROID)
#		pragma message("GLM: Android platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_LINUX)
#		pragma message("GLM: Linux platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_UNIX)
#		pragma message("GLM: UNIX platform detected")
#	elif(GLM_PLATFORM & GLM_PLATFORM_UNKNOWN)
#		pragma message("GLM: platform unknown")
#	else
#		pragma message("GLM: platform not detected")
#	endif
#endif//GLM_MESSAGE

///////////////////////////////////////////////////////////////////////////////////
// Compiler

#define GLM_COMPILER_UNKNOWN		0x00000000

// Intel
#define GLM_COMPILER_INTEL			0x00100000
#define GLM_COMPILER_INTEL12		0x00100010
#define GLM_COMPILER_INTEL12_1		0x00100020
#define GLM_COMPILER_INTEL13		0x00100030
#define GLM_COMPILER_INTEL14		0x00100040
#define GLM_COMPILER_INTEL15		0x00100050
#define GLM_COMPILER_INTEL16		0x00100060

// Visual C++ defines
#define GLM_COMPILER_VC				0x01000000
#define GLM_COMPILER_VC2010			0x01000090
#define GLM_COMPILER_VC2012			0x010000A0
#define GLM_COMPILER_VC2013			0x010000B0
#define GLM_COMPILER_VC2015			0x010000C0

// GCC defines
#define GLM_COMPILER_GCC			0x02000000
#define GLM_COMPILER_GCC44			0x020000B0
#define GLM_COMPILER_GCC45			0x020000C0
#define GLM_COMPILER_GCC46			0x020000D0
#define GLM_COMPILER_GCC47			0x020000E0
#define GLM_COMPILER_GCC48			0x020000F0
#define GLM_COMPILER_GCC49			0x02000100
#define GLM_COMPILER_GCC50			0x02000200
#define GLM_COMPILER_GCC51			0x02000300
#define GLM_COMPILER_GCC52			0x02000400
#define GLM_COMPILER_GCC53			0x02000500
#define GLM_COMPILER_GCC60			0x02000600

// CUDA
#define GLM_COMPILER_CUDA			0x10000000
#define GLM_COMPILER_CUDA40			0x10000040
#define GLM_COMPILER_CUDA41			0x10000050
#define GLM_COMPILER_CUDA42			0x10000060
#define GLM_COMPILER_CUDA50			0x10000070
#define GLM_COMPILER_CUDA60			0x10000080
#define GLM_COMPILER_CUDA65			0x10000090
#define GLM_COMPILER_CUDA70			0x100000A0
#define GLM_COMPILER_CUDA75			0x100000B0

// LLVM
#define GLM_COMPILER_LLVM			0x20000000
#define GLM_COMPILER_LLVM32			0x20000030
#define GLM_COMPILER_LLVM33			0x20000040
#define GLM_COMPILER_LLVM34			0x20000050
#define GLM_COMPILER_LLVM35			0x20000060
#define GLM_COMPILER_LLVM36			0x20000070
#define GLM_COMPILER_LLVM37			0x20000080
#define GLM_COMPILER_LLVM38			0x20000090
#define GLM_COMPILER_LLVM39			0x200000A0

// Build model
#define GLM_MODEL_32				0x00000010
#define GLM_MODEL_64				0x00000020

// Force generic C++ compiler
#ifdef GLM_FORCE_COMPILER_UNKNOWN
#	define GLM_COMPILER GLM_COMPILER_UNKNOWN

#elif defined(__INTEL_COMPILER)
#	if __INTEL_COMPILER == 1200
#		define GLM_COMPILER GLM_COMPILER_INTEL12
#	elif __INTEL_COMPILER == 1210
#		define GLM_COMPILER GLM_COMPILER_INTEL12_1
#	elif __INTEL_COMPILER == 1300
#		define GLM_COMPILER GLM_COMPILER_INTEL13
#	elif __INTEL_COMPILER == 1400
#		define GLM_COMPILER GLM_COMPILER_INTEL14
#	elif __INTEL_COMPILER == 1500
#		define GLM_COMPILER GLM_COMPILER_INTEL15
#	elif __INTEL_COMPILER >= 1600
#		define GLM_COMPILER GLM_COMPILER_INTEL16
#	else
#		define GLM_COMPILER GLM_COMPILER_INTEL
#	endif

// CUDA
#elif defined(__CUDACC__)
#	if !defined(CUDA_VERSION) && !defined(GLM_FORCE_CUDA)
#		include <cuda.h>  // make sure version is defined since nvcc does not define it itself!
#	endif
#	if CUDA_VERSION < 3000
#		error "GLM requires CUDA 3.0 or higher"
#	else
#		define GLM_COMPILER GLM_COMPILER_CUDA
#	endif

// Clang
#elif defined(__clang__)
#	if GLM_PLATFORM & GLM_PLATFORM_APPLE
#		if __clang_major__ == 5 && __clang_minor__ == 0
#			define GLM_COMPILER GLM_COMPILER_LLVM33
#		elif __clang_major__ == 5 && __clang_minor__ == 1
#			define GLM_COMPILER GLM_COMPILER_LLVM34
#		elif __clang_major__ == 6 && __clang_minor__ == 0
#			define GLM_COMPILER GLM_COMPILER_LLVM35
#		elif __clang_major__ == 6 && __clang_minor__ >= 1
#			define GLM_COMPILER GLM_COMPILER_LLVM36
#		elif __clang_major__ >= 7
#			define GLM_COMPILER GLM_COMPILER_LLVM37
#		else
#			define GLM_COMPILER GLM_COMPILER_LLVM
#		endif
#	else
#		if __clang_major__ == 3 && __clang_minor__ == 0
#			define GLM_COMPILER GLM_COMPILER_LLVM30
#		elif __clang_major__ == 3 && __clang_minor__ == 1
#			define GLM_COMPILER GLM_COMPILER_LLVM31
#		elif __clang_major__ == 3 && __clang_minor__ == 2
#			define GLM_COMPILER GLM_COMPILER_LLVM32
#		elif __clang_major__ == 3 && __clang_minor__ == 3
#			define GLM_COMPILER GLM_COMPILER_LLVM33
#		elif __clang_major__ == 3 && __clang_minor__ == 4
#			define GLM_COMPILER GLM_COMPILER_LLVM34
#		elif __clang_major__ == 3 && __clang_minor__ == 5
#			define GLM_COMPILER GLM_COMPILER_LLVM35
#		elif __clang_major__ == 3 && __clang_minor__ == 6
#			define GLM_COMPILER GLM_COMPILER_LLVM36
#		elif __clang_major__ == 3 && __clang_minor__ == 7
#			define GLM_COMPILER GLM_COMPILER_LLVM37
#		elif __clang_major__ == 3 && __clang_minor__ == 8
#			define GLM_COMPILER GLM_COMPILER_LLVM38
#		elif __clang_major__ == 3 && __clang_minor__ >= 9
#			define GLM_COMPILER GLM_COMPILER_LLVM39
#		elif __clang_major__ >= 4
#			define GLM_COMPILER GLM_COMPILER_LLVM39
#		else
#			define GLM_COMPILER GLM_COMPILER_LLVM
#		endif
#	endif

// Visual C++
#elif defined(_MSC_VER)
#	if _MSC_VER < 1600
#		error "GLM requires Visual C++ 2010 or higher"
#	elif _MSC_VER == 1600
#		define GLM_COMPILER GLM_COMPILER_VC2010
#	elif _MSC_VER == 1700
#		define GLM_COMPILER GLM_COMPILER_VC2012
#	elif _MSC_VER == 1800
#		define GLM_COMPILER GLM_COMPILER_VC2013
#	elif _MSC_VER >= 1900
#		define GLM_COMPILER GLM_COMPILER_VC2015
#	else//_MSC_VER
#		define GLM_COMPILER GLM_COMPILER_VC
#	endif//_MSC_VER

// G++
#elif defined(__GNUC__) || defined(__MINGW32__)
#	if (__GNUC__ == 4) && (__GNUC_MINOR__ == 2)
#		define GLM_COMPILER (GLM_COMPILER_GCC42)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 3)
#		define GLM_COMPILER (GLM_COMPILER_GCC43)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 4)
#		define GLM_COMPILER (GLM_COMPILER_GCC44)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 5)
#		define GLM_COMPILER (GLM_COMPILER_GCC45)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 6)
#		define GLM_COMPILER (GLM_COMPILER_GCC46)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 7)
#		define GLM_COMPILER (GLM_COMPILER_GCC47)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ == 8)
#		define GLM_COMPILER (GLM_COMPILER_GCC48)
#	elif (__GNUC__ == 4) && (__GNUC_MINOR__ >= 9)
#		define GLM_COMPILER (GLM_COMPILER_GCC49)
#	elif (__GNUC__ == 5) && (__GNUC_MINOR__ == 0)
#		define GLM_COMPILER (GLM_COMPILER_GCC50)
#	elif (__GNUC__ == 5) && (__GNUC_MINOR__ == 1)
#		define GLM_COMPILER (GLM_COMPILER_GCC51)
#	elif (__GNUC__ == 5) && (__GNUC_MINOR__ == 2)
#		define GLM_COMPILER (GLM_COMPILER_GCC52)
#	elif (__GNUC__ == 5) && (__GNUC_MINOR__ >= 3)
#		define GLM_COMPILER (GLM_COMPILER_GCC53)
#	elif (__GNUC__ >= 6)
#		define GLM_COMPILER (GLM_COMPILER_GCC60)
#	else
#		define GLM_COMPILER (GLM_COMPILER_GCC)
#	endif

#else
#	define GLM_COMPILER GLM_COMPILER_UNKNOWN
#endif

#ifndef GLM_COMPILER
#	error "GLM_COMPILER undefined, your compiler may not be supported by GLM. Add #define GLM_COMPILER 0 to ignore this message."
#endif//GLM_COMPILER
