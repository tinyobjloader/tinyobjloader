///////////////////////////////////////////////////////////////////////////////////
/// OpenGL Mathematics (glm.g-truc.net)
///
/// Copyright (c) 2005 - 2015 G-Truc Creation (www.g-truc.net)
/// Permission is hereby granted, free of charge, to any person obtaining a copy
/// of this software and associated documentation files (the "Software"), to deal
/// in the Software without restriction, including without limitation the rights
/// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
/// copies of the Software, and to permit persons to whom the Software is
/// furnished to do so, subject to the following conditions:
/// 
/// The above copyright notice and this permission notice shall be included in
/// all copies or substantial portions of the Software.
/// 
/// Restrictions:
///		By making use of the Software for military purposes, you choose to make
///		a Bunny unhappy.
/// 
/// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
/// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
/// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
/// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
/// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
/// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
/// THE SOFTWARE.
///
/// @file test/gtc/gtc_bitfield.cpp
/// @date 2014-10-25 / 2014-11-25
/// @author Christophe Riccio
///////////////////////////////////////////////////////////////////////////////////

#include <glm/gtc/bitfield.hpp>
#include <glm/gtc/type_precision.hpp>
#include <glm/vector_relational.hpp>
#if GLM_ARCH != GLM_ARCH_PURE
#	include <glm/detail/intrinsic_integer.hpp>
#endif
#include <ctime>
#include <cstdio>
#include <vector>

namespace mask
{
	template <typename genType>
	struct type
	{
		genType		Value;
		genType		Return;
	};

	inline int mask_zero(int Bits)
	{
		return ~((~0) << Bits);
	}

	inline int mask_mix(int Bits)
	{
		return Bits >= sizeof(int) * 8 ? 0xffffffff : (static_cast<int>(1) << Bits) - static_cast<int>(1);
	}

	inline int mask_half(int Bits)
	{
		// We do the shift in two steps because 1 << 32 on an int is undefined.

		int const Half = Bits >> 1;
		int const Fill = ~0;
		int const ShiftHaft = (Fill << Half);
		int const Rest = Bits - Half;
		int const Reversed = ShiftHaft << Rest;

		return ~Reversed;
	}

	inline int mask_loop(int Bits)
	{
		int Mask = 0;
		for(int Bit = 0; Bit < Bits; ++Bit)
			Mask |= (static_cast<int>(1) << Bit);
		return Mask;
	}

	int perf()
	{
		int const Count = 100000000;

		std::clock_t Timestamp1 = std::clock();

		{
			std::vector<int> Mask;
			Mask.resize(Count);
			for(int i = 0; i < Count; ++i)
				Mask[i] = mask_mix(i % 32);
		}

		std::clock_t Timestamp2 = std::clock();

		{
			std::vector<int> Mask;
			Mask.resize(Count);
			for(int i = 0; i < Count; ++i)
				Mask[i] = mask_loop(i % 32);
		}

		std::clock_t Timestamp3 = std::clock();

		{
			std::vector<int> Mask;
			Mask.resize(Count);
			for(int i = 0; i < Count; ++i)
				Mask[i] = glm::mask(i % 32);
		}

		std::clock_t Timestamp4 = std::clock();

		{
			std::vector<int> Mask;
			Mask.resize(Count);
			for(int i = 0; i < Count; ++i)
				Mask[i] = mask_zero(i % 32);
		}

		std::clock_t Timestamp5 = std::clock();

		{
			std::vector<int> Mask;
			Mask.resize(Count);
			for(int i = 0; i < Count; ++i)
				Mask[i] = mask_half(i % 32);
		}

		std::clock_t Timestamp6 = std::clock();

		std::clock_t TimeMix = Timestamp2 - Timestamp1;
		std::clock_t TimeLoop = Timestamp3 - Timestamp2;
		std::clock_t TimeDefault = Timestamp4 - Timestamp3;
		std::clock_t TimeZero = Timestamp5 - Timestamp4;
		std::clock_t TimeHalf = Timestamp6 - Timestamp5;

		printf("mask[mix]: %d\n", static_cast<unsigned int>(TimeMix));
		printf("mask[loop]: %d\n", static_cast<unsigned int>(TimeLoop));
		printf("mask[default]: %d\n", static_cast<unsigned int>(TimeDefault));
		printf("mask[zero]: %d\n", static_cast<unsigned int>(TimeZero));
		printf("mask[half]: %d\n", static_cast<unsigned int>(TimeHalf));

		return TimeDefault < TimeLoop ? 0 : 1;
	}

	int test_uint()
	{
		type<glm::uint> const Data[] =
		{
			{ 0, 0x00000000},
			{ 1, 0x00000001},
			{ 2, 0x00000003},
			{ 3, 0x00000007},
			{31, 0x7fffffff},
			{32, 0xffffffff}
		};

		int Error(0);
/* mask_zero is sadly not a correct code
		for(std::size_t i = 0; i < sizeof(Data) / sizeof(type<int>); ++i)
		{
			int Result = mask_zero(Data[i].Value);
			Error += Data[i].Return == Result ? 0 : 1;
		}
*/
		for(std::size_t i = 0; i < sizeof(Data) / sizeof(type<int>); ++i)
		{
			int Result = mask_mix(Data[i].Value);
			Error += Data[i].Return == Result ? 0 : 1;
		}

		for(std::size_t i = 0; i < sizeof(Data) / sizeof(type<int>); ++i)
		{
			int Result = mask_half(Data[i].Value);
			Error += Data[i].Return == Result ? 0 : 1;
		}

		for(std::size_t i = 0; i < sizeof(Data) / sizeof(type<int>); ++i)
		{
			int Result = mask_loop(Data[i].Value);
			Error += Data[i].Return == Result ? 0 : 1;
		}

		for(std::size_t i = 0; i < sizeof(Data) / sizeof(type<int>); ++i)
		{
			int Result = glm::mask(Data[i].Value);
			Error += Data[i].Return == Result ? 0 : 1;
		}

		return Error;
	}

	int test_uvec4()
	{
		type<glm::ivec4> const Data[] =
		{
			{glm::ivec4( 0), glm::ivec4(0x00000000)},
			{glm::ivec4( 1), glm::ivec4(0x00000001)},
			{glm::ivec4( 2), glm::ivec4(0x00000003)},
			{glm::ivec4( 3), glm::ivec4(0x00000007)},
			{glm::ivec4(31), glm::ivec4(0x7fffffff)},
			{glm::ivec4(32), glm::ivec4(0xffffffff)}
		};

		int Error(0);

		for(std::size_t i = 0, n = sizeof(Data) / sizeof(type<glm::ivec4>); i < n; ++i)
		{
			glm::ivec4 Result = glm::mask(Data[i].Value);
			Error += glm::all(glm::equal(Data[i].Return, Result)) ? 0 : 1;
		}

		return Error;
	}

	int test()
	{
		int Error(0);

		Error += test_uint();
		Error += test_uvec4();

		return Error;
	}
}//namespace mask

namespace bitfieldInterleave3
{
	template <typename PARAM, typename RET>
	inline RET refBitfieldInterleave(PARAM x, PARAM y, PARAM z)
	{
		RET Result = 0; 
		for(RET i = 0; i < sizeof(PARAM) * 8; ++i)
		{
			Result |= ((RET(x) & (RET(1U) << i)) << ((i << 1) + 0));
			Result |= ((RET(y) & (RET(1U) << i)) << ((i << 1) + 1));
			Result |= ((RET(z) & (RET(1U) << i)) << ((i << 1) + 2));
		}
		return Result;
	}

	int test()
	{
		int Error(0);

		glm::uint16 x_max = 1 << 11;
		glm::uint16 y_max = 1 << 11;
		glm::uint16 z_max = 1 << 11;

		for(glm::uint16 z = 0; z < z_max; z += 27)
		for(glm::uint16 y = 0; y < y_max; y += 27)
		for(glm::uint16 x = 0; x < x_max; x += 27)
		{
			glm::uint64 ResultA = refBitfieldInterleave<glm::uint16, glm::uint64>(x, y, z);
			glm::uint64 ResultB = glm::bitfieldInterleave(x, y, z);
			Error += ResultA == ResultB ? 0 : 1;
		}

		return Error;
	}
}

namespace bitfieldInterleave4
{
	template <typename PARAM, typename RET>
	inline RET loopBitfieldInterleave(PARAM x, PARAM y, PARAM z, PARAM w)
	{
		RET const v[4] = {x, y, z, w};
		RET Result = 0; 
		for(RET i = 0; i < sizeof(PARAM) * 8; i++)
		{
			Result |= ((((v[0] >> i) & 1U)) << ((i << 2) + 0));
			Result |= ((((v[1] >> i) & 1U)) << ((i << 2) + 1));
			Result |= ((((v[2] >> i) & 1U)) << ((i << 2) + 2));
			Result |= ((((v[3] >> i) & 1U)) << ((i << 2) + 3));
		}
		return Result;
	}

	int test()
	{
		int Error(0);

		glm::uint16 x_max = 1 << 11;
		glm::uint16 y_max = 1 << 11;
		glm::uint16 z_max = 1 << 11;
		glm::uint16 w_max = 1 << 11;

		for(glm::uint16 w = 0; w < w_max; w += 27)
		for(glm::uint16 z = 0; z < z_max; z += 27)
		for(glm::uint16 y = 0; y < y_max; y += 27)
		for(glm::uint16 x = 0; x < x_max; x += 27)
		{
			glm::uint64 ResultA = loopBitfieldInterleave<glm::uint16, glm::uint64>(x, y, z, w);
			glm::uint64 ResultB = glm::bitfieldInterleave(x, y, z, w);
			Error += ResultA == ResultB ? 0 : 1;
		}

		return Error;
	}
}

namespace bitfieldInterleave
{
	inline glm::uint64 fastBitfieldInterleave(glm::uint32 x, glm::uint32 y)
	{
		glm::uint64 REG1;
		glm::uint64 REG2;

		REG1 = x;
		REG1 = ((REG1 << 16) | REG1) & glm::uint64(0x0000FFFF0000FFFF);
		REG1 = ((REG1 <<  8) | REG1) & glm::uint64(0x00FF00FF00FF00FF);
		REG1 = ((REG1 <<  4) | REG1) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		REG1 = ((REG1 <<  2) | REG1) & glm::uint64(0x3333333333333333);
		REG1 = ((REG1 <<  1) | REG1) & glm::uint64(0x5555555555555555);

		REG2 = y;
		REG2 = ((REG2 << 16) | REG2) & glm::uint64(0x0000FFFF0000FFFF);
		REG2 = ((REG2 <<  8) | REG2) & glm::uint64(0x00FF00FF00FF00FF);
		REG2 = ((REG2 <<  4) | REG2) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		REG2 = ((REG2 <<  2) | REG2) & glm::uint64(0x3333333333333333);
		REG2 = ((REG2 <<  1) | REG2) & glm::uint64(0x5555555555555555);

		return REG1 | (REG2 << 1);
	}

	inline glm::uint64 interleaveBitfieldInterleave(glm::uint32 x, glm::uint32 y)
	{
		glm::uint64 REG1;
		glm::uint64 REG2;

		REG1 = x;
		REG2 = y;

		REG1 = ((REG1 << 16) | REG1) & glm::uint64(0x0000FFFF0000FFFF);
		REG2 = ((REG2 << 16) | REG2) & glm::uint64(0x0000FFFF0000FFFF);

		REG1 = ((REG1 <<  8) | REG1) & glm::uint64(0x00FF00FF00FF00FF);
		REG2 = ((REG2 <<  8) | REG2) & glm::uint64(0x00FF00FF00FF00FF);

		REG1 = ((REG1 <<  4) | REG1) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		REG2 = ((REG2 <<  4) | REG2) & glm::uint64(0x0F0F0F0F0F0F0F0F);

		REG1 = ((REG1 <<  2) | REG1) & glm::uint64(0x3333333333333333);
		REG2 = ((REG2 <<  2) | REG2) & glm::uint64(0x3333333333333333);

		REG1 = ((REG1 <<  1) | REG1) & glm::uint64(0x5555555555555555);
		REG2 = ((REG2 <<  1) | REG2) & glm::uint64(0x5555555555555555);

		return REG1 | (REG2 << 1);
	}

	inline glm::uint64 loopBitfieldInterleave(glm::uint32 x, glm::uint32 y)
	{
		static glm::uint64 const Mask[5] = 
		{
			0x5555555555555555,
			0x3333333333333333,
			0x0F0F0F0F0F0F0F0F,
			0x00FF00FF00FF00FF,
			0x0000FFFF0000FFFF
		};

		glm::uint64 REG1 = x;
		glm::uint64 REG2 = y;
		for(int i = 4; i >= 0; --i)
		{
			REG1 = ((REG1 << (1 << i)) | REG1) & Mask[i];
			REG2 = ((REG2 << (1 << i)) | REG2) & Mask[i];
		}

		return REG1 | (REG2 << 1);
	}

#if(GLM_ARCH != GLM_ARCH_PURE)
	inline glm::uint64 sseBitfieldInterleave(glm::uint32 x, glm::uint32 y)
	{
		GLM_ALIGN(16) glm::uint32 const Array[4] = {x, 0, y, 0};

		__m128i const Mask4 = _mm_set1_epi32(0x0000FFFF);
		__m128i const Mask3 = _mm_set1_epi32(0x00FF00FF);
		__m128i const Mask2 = _mm_set1_epi32(0x0F0F0F0F);
		__m128i const Mask1 = _mm_set1_epi32(0x33333333);
		__m128i const Mask0 = _mm_set1_epi32(0x55555555);

		__m128i Reg1;
		__m128i Reg2;

		// REG1 = x;
		// REG2 = y;
		Reg1 = _mm_load_si128((__m128i*)Array);

		//REG1 = ((REG1 << 16) | REG1) & glm::uint64(0x0000FFFF0000FFFF);
		//REG2 = ((REG2 << 16) | REG2) & glm::uint64(0x0000FFFF0000FFFF);
		Reg2 = _mm_slli_si128(Reg1, 2);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask4);

		//REG1 = ((REG1 <<  8) | REG1) & glm::uint64(0x00FF00FF00FF00FF);
		//REG2 = ((REG2 <<  8) | REG2) & glm::uint64(0x00FF00FF00FF00FF);
		Reg2 = _mm_slli_si128(Reg1, 1);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask3);

		//REG1 = ((REG1 <<  4) | REG1) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		//REG2 = ((REG2 <<  4) | REG2) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		Reg2 = _mm_slli_epi32(Reg1, 4);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask2);

		//REG1 = ((REG1 <<  2) | REG1) & glm::uint64(0x3333333333333333);
		//REG2 = ((REG2 <<  2) | REG2) & glm::uint64(0x3333333333333333);
		Reg2 = _mm_slli_epi32(Reg1, 2);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask1);

		//REG1 = ((REG1 <<  1) | REG1) & glm::uint64(0x5555555555555555);
		//REG2 = ((REG2 <<  1) | REG2) & glm::uint64(0x5555555555555555);
		Reg2 = _mm_slli_epi32(Reg1, 1);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask0);

		//return REG1 | (REG2 << 1);
		Reg2 = _mm_slli_epi32(Reg1, 1);
		Reg2 = _mm_srli_si128(Reg2, 8);
		Reg1 = _mm_or_si128(Reg1, Reg2);
	
		GLM_ALIGN(16) glm::uint64 Result[2];
		_mm_store_si128((__m128i*)Result, Reg1);

		return Result[0];
	}

	inline glm::uint64 sseUnalignedBitfieldInterleave(glm::uint32 x, glm::uint32 y)
	{
		glm::uint32 const Array[4] = {x, 0, y, 0};

		__m128i const Mask4 = _mm_set1_epi32(0x0000FFFF);
		__m128i const Mask3 = _mm_set1_epi32(0x00FF00FF);
		__m128i const Mask2 = _mm_set1_epi32(0x0F0F0F0F);
		__m128i const Mask1 = _mm_set1_epi32(0x33333333);
		__m128i const Mask0 = _mm_set1_epi32(0x55555555);

		__m128i Reg1;
		__m128i Reg2;

		// REG1 = x;
		// REG2 = y;
		Reg1 = _mm_loadu_si128((__m128i*)Array);

		//REG1 = ((REG1 << 16) | REG1) & glm::uint64(0x0000FFFF0000FFFF);
		//REG2 = ((REG2 << 16) | REG2) & glm::uint64(0x0000FFFF0000FFFF);
		Reg2 = _mm_slli_si128(Reg1, 2);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask4);

		//REG1 = ((REG1 <<  8) | REG1) & glm::uint64(0x00FF00FF00FF00FF);
		//REG2 = ((REG2 <<  8) | REG2) & glm::uint64(0x00FF00FF00FF00FF);
		Reg2 = _mm_slli_si128(Reg1, 1);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask3);

		//REG1 = ((REG1 <<  4) | REG1) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		//REG2 = ((REG2 <<  4) | REG2) & glm::uint64(0x0F0F0F0F0F0F0F0F);
		Reg2 = _mm_slli_epi32(Reg1, 4);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask2);

		//REG1 = ((REG1 <<  2) | REG1) & glm::uint64(0x3333333333333333);
		//REG2 = ((REG2 <<  2) | REG2) & glm::uint64(0x3333333333333333);
		Reg2 = _mm_slli_epi32(Reg1, 2);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask1);

		//REG1 = ((REG1 <<  1) | REG1) & glm::uint64(0x5555555555555555);
		//REG2 = ((REG2 <<  1) | REG2) & glm::uint64(0x5555555555555555);
		Reg2 = _mm_slli_epi32(Reg1, 1);
		Reg1 = _mm_or_si128(Reg2, Reg1);
		Reg1 = _mm_and_si128(Reg1, Mask0);

		//return REG1 | (REG2 << 1);
		Reg2 = _mm_slli_epi32(Reg1, 1);
		Reg2 = _mm_srli_si128(Reg2, 8);
		Reg1 = _mm_or_si128(Reg1, Reg2);
	
		glm::uint64 Result[2];
		_mm_storeu_si128((__m128i*)Result, Reg1);

		return Result[0];
	}
#endif//(GLM_ARCH != GLM_ARCH_PURE)

	int test()
	{
		{
			for(glm::uint32 y = 0; y < (1 << 10); ++y)
			for(glm::uint32 x = 0; x < (1 << 10); ++x)
			{
				glm::uint64 A = glm::bitfieldInterleave(x, y);
				glm::uint64 B = fastBitfieldInterleave(x, y);
				glm::uint64 C = loopBitfieldInterleave(x, y);
				glm::uint64 D = interleaveBitfieldInterleave(x, y);

				assert(A == B);
				assert(A == C);
				assert(A == D);

#				if(GLM_ARCH != GLM_ARCH_PURE)
					glm::uint64 E = sseBitfieldInterleave(x, y);
					glm::uint64 F = sseUnalignedBitfieldInterleave(x, y);
					assert(A == E);
					assert(A == F);

					__m128i G = glm::detail::_mm_bit_interleave_si128(_mm_set_epi32(0, y, 0, x));
					glm::uint64 Result[2];
					_mm_storeu_si128((__m128i*)Result, G);
					assert(A == Result[0]);
#				endif//(GLM_ARCH != GLM_ARCH_PURE)
			}
		}

		{
			for(glm::uint8 y = 0; y < 127; ++y)
			for(glm::uint8 x = 0; x < 127; ++x)
			{
				glm::uint64 A(glm::bitfieldInterleave(glm::uint8(x), glm::uint8(y)));
				glm::uint64 B(glm::bitfieldInterleave(glm::uint16(x), glm::uint16(y)));
				glm::uint64 C(glm::bitfieldInterleave(glm::uint32(x), glm::uint32(y)));

				glm::int64 D(glm::bitfieldInterleave(glm::int8(x), glm::int8(y)));
				glm::int64 E(glm::bitfieldInterleave(glm::int16(x), glm::int16(y)));
				glm::int64 F(glm::bitfieldInterleave(glm::int32(x), glm::int32(y)));

				assert(D == E);
				assert(D == F);
			}
		}

		return 0;
	}

	int perf()
	{
		glm::uint32 x_max = 1 << 11;
		glm::uint32 y_max = 1 << 10;

		// ALU
		std::vector<glm::uint64> Data(x_max * y_max);
		std::vector<glm::u32vec2> Param(x_max * y_max);
		for(glm::uint32 i = 0; i < Param.size(); ++i)
			Param[i] = glm::u32vec2(i % x_max, i / y_max);

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = glm::bitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("glm::bitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = fastBitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("fastBitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = loopBitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("loopBitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = interleaveBitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("interleaveBitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

#		if(GLM_ARCH != GLM_ARCH_PURE)
		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = sseBitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("sseBitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = sseUnalignedBitfieldInterleave(Param[i].x, Param[i].y);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("sseUnalignedBitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}
#		endif//(GLM_ARCH != GLM_ARCH_PURE)

		{
			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < Data.size(); ++i)
				Data[i] = glm::bitfieldInterleave(Param[i].x, Param[i].y, Param[i].x);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("glm::detail::bitfieldInterleave Time %d clocks\n", static_cast<unsigned int>(Time));
		}

#		if(GLM_ARCH != GLM_ARCH_PURE && !(GLM_COMPILER & GLM_COMPILER_GCC))
		{
			// SIMD
			std::vector<__m128i> SimdData;
			SimdData.resize(x_max * y_max);
			std::vector<__m128i> SimdParam;
			SimdParam.resize(x_max * y_max);
			for(int i = 0; i < SimdParam.size(); ++i)
				SimdParam[i] = _mm_set_epi32(i % x_max, 0, i / y_max, 0);

			std::clock_t LastTime = std::clock();

			for(std::size_t i = 0; i < SimdData.size(); ++i)
				SimdData[i] = glm::detail::_mm_bit_interleave_si128(SimdParam[i]);

			std::clock_t Time = std::clock() - LastTime;

			std::printf("_mm_bit_interleave_si128 Time %d clocks\n", static_cast<unsigned int>(Time));
		}
#		endif//(GLM_ARCH != GLM_ARCH_PURE)

		return 0;
	}
}//namespace bitfieldInterleave

int main()
{
	int Error(0);

	Error += ::mask::test();
	Error += ::bitfieldInterleave3::test();
	Error += ::bitfieldInterleave4::test();
	Error += ::bitfieldInterleave::test();
	//Error += ::bitRevert::test();

#	ifdef NDEBUG
		Error += ::mask::perf();
		Error += ::bitfieldInterleave::perf();
#	endif//NDEBUG

	return Error;
}
