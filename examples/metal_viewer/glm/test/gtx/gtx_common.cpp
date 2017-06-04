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
/// @file test/gtx/gtx_common.cpp
/// @date 2014-09-08 / 2014-11-25
/// @author Christophe Riccio
///////////////////////////////////////////////////////////////////////////////////

#include <glm/gtx/common.hpp>
#include <glm/gtc/integer.hpp>
#include <glm/gtc/epsilon.hpp>
#include <glm/vector_relational.hpp>
#include <glm/common.hpp>

namespace fmod_
{
	template <typename genType>
	GLM_FUNC_QUALIFIER genType modTrunc(genType a, genType b)
	{
		return a - b * glm::trunc(a / b);
	}

	int test()
	{
		int Error(0);

		{
			float A0(3.0);
			float B0(2.0f);
			float C0 = glm::fmod(A0, B0);

			Error += glm::abs(C0 - 1.0f) < 0.00001f ? 0 : 1;

			glm::vec4 A1(3.0);
			float B1(2.0f);
			glm::vec4 C1 = glm::fmod(A1, B1);

			Error += glm::all(glm::epsilonEqual(C1, glm::vec4(1.0f), 0.00001f)) ? 0 : 1;

			glm::vec4 A2(3.0);
			glm::vec4 B2(2.0f);
			glm::vec4 C2 = glm::fmod(A2, B2);

			Error += glm::all(glm::epsilonEqual(C2, glm::vec4(1.0f), 0.00001f)) ? 0 : 1;

			glm::ivec4 A3(3);
			int B3(2);
			glm::ivec4 C3 = glm::fmod(A3, B3);

			Error += glm::all(glm::equal(C3, glm::ivec4(1))) ? 0 : 1;

			glm::ivec4 A4(3);
			glm::ivec4 B4(2);
			glm::ivec4 C4 = glm::fmod(A4, B4);

			Error += glm::all(glm::equal(C4, glm::ivec4(1))) ? 0 : 1;
		}

		{
			float A0(22.0);
			float B0(-10.0f);
			float C0 = glm::fmod(A0, B0);

			Error += glm::abs(C0 - 2.0f) < 0.00001f ? 0 : 1;

			glm::vec4 A1(22.0);
			float B1(-10.0f);
			glm::vec4 C1 = glm::fmod(A1, B1);

			Error += glm::all(glm::epsilonEqual(C1, glm::vec4(2.0f), 0.00001f)) ? 0 : 1;

			glm::vec4 A2(22.0);
			glm::vec4 B2(-10.0f);
			glm::vec4 C2 = glm::fmod(A2, B2);

			Error += glm::all(glm::epsilonEqual(C2, glm::vec4(2.0f), 0.00001f)) ? 0 : 1;

			glm::ivec4 A3(22);
			int B3(-10);
			glm::ivec4 C3 = glm::fmod(A3, B3);

			Error += glm::all(glm::equal(C3, glm::ivec4(2))) ? 0 : 1;

			glm::ivec4 A4(22);
			glm::ivec4 B4(-10);
			glm::ivec4 C4 = glm::fmod(A4, B4);

			Error += glm::all(glm::equal(C4, glm::ivec4(2))) ? 0 : 1;
		}

		// http://stackoverflow.com/questions/7610631/glsl-mod-vs-hlsl-fmod
		{
			for (float y = -10.0f; y < 10.0f; y += 0.1f)
			for (float x = -10.0f; x < 10.0f; x += 0.1f)
			{
				float const A(std::fmod(x, y));
				//float const B(std::remainder(x, y));
				float const C(glm::fmod(x, y));
				float const D(modTrunc(x, y));

				//Error += glm::epsilonEqual(A, B, 0.0001f) ? 0 : 1;
				//assert(!Error);
				Error += glm::epsilonEqual(A, C, 0.0001f) ? 0 : 1;
				assert(!Error);
				Error += glm::epsilonEqual(A, D, 0.00001f) ? 0 : 1;
				assert(!Error);
			}
		}

		return Error;
	}
}//namespace fmod_

int test_isdenormal()
{
	int Error(0);

	bool A = glm::isdenormal(1.0f);
	glm::bvec1 B = glm::isdenormal(glm::vec1(1.0f));
	glm::bvec2 C = glm::isdenormal(glm::vec2(1.0f));
	glm::bvec3 D = glm::isdenormal(glm::vec3(1.0f));
	glm::bvec4 E = glm::isdenormal(glm::vec4(1.0f));

	return Error;
}

int main()
{
	int Error(0);

	Error += test_isdenormal();
	Error += ::fmod_::test();

	return Error;
}
