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
/// @ref gtx_norm
/// @file glm/gtx/norm.inl
/// @date 2005-12-21 / 2008-07-24
/// @author Christophe Riccio
///////////////////////////////////////////////////////////////////////////////////

namespace glm{
namespace detail
{
	template <template <typename, precision> class vecType, typename T, precision P>
	struct compute_length2
	{
		GLM_FUNC_QUALIFIER static T call(vecType<T, P> const & v)
		{
			return dot(v, v);
		}
	};
}//namespace detail

	template <typename genType>
	GLM_FUNC_QUALIFIER genType length2(genType x)
	{
		GLM_STATIC_ASSERT(std::numeric_limits<genType>::is_iec559, "'length2' accepts only floating-point inputs");
		return x * x;
	}

	template <typename T, precision P, template <typename, precision> class vecType>
	GLM_FUNC_QUALIFIER T length2(vecType<T, P> const & v)
	{
		GLM_STATIC_ASSERT(std::numeric_limits<T>::is_iec559, "'length2' accepts only floating-point inputs");
		return detail::compute_length2<vecType, T, P>::call(v);
	}

	template <typename T>
	GLM_FUNC_QUALIFIER T distance2(T p0, T p1)
	{
		GLM_STATIC_ASSERT(std::numeric_limits<T>::is_iec559, "'distance2' accepts only floating-point inputs");
		return length2(p1 - p0);
	}

	template <typename T, precision P, template <typename, precision> class vecType>
	GLM_FUNC_QUALIFIER T distance2(vecType<T, P> const & p0, vecType<T, P> const & p1)
	{
		GLM_STATIC_ASSERT(std::numeric_limits<T>::is_iec559, "'distance2' accepts only floating-point inputs");
		return length2(p1 - p0);
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T l1Norm
	(
		tvec3<T, P> const & a,
		tvec3<T, P> const & b
	)
	{
		return abs(b.x - a.x) + abs(b.y - a.y) + abs(b.z - a.z);
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T l1Norm
	(
		tvec3<T, P> const & v
	)
	{
		return abs(v.x) + abs(v.y) + abs(v.z);
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T l2Norm
	(
		tvec3<T, P> const & a,
		tvec3<T, P> const & b
	)
	{
		return length(b - a);
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T l2Norm
	(
		tvec3<T, P> const & v
	)
	{
		return length(v);
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T lxNorm
	(
		tvec3<T, P> const & x,
		tvec3<T, P> const & y,
		unsigned int Depth
	)
	{
		return pow(pow(y.x - x.x, T(Depth)) + pow(y.y - x.y, T(Depth)) + pow(y.z - x.z, T(Depth)), T(1) / T(Depth));
	}

	template <typename T, precision P>
	GLM_FUNC_QUALIFIER T lxNorm
	(
		tvec3<T, P> const & v,
		unsigned int Depth
	)
	{
		return pow(pow(v.x, T(Depth)) + pow(v.y, T(Depth)) + pow(v.z, T(Depth)), T(1) / T(Depth));
	}

}//namespace glm
