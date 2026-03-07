// obj_parse_float.h - OBJ-specific float parser built on fast_float.
//
// Handles OBJ quirks:
//   - Leading '+' sign  (e.g. "+1.0", "+0.5e+2")
//   - nan / NaN / NAN   (case-insensitive)
//   - inf / Inf / INF / infinity (case-insensitive, with optional sign)
//
// Non-finite replacement (NumPy-style defaults):
//   nan  ->  0.0
//   inf  ->  std::numeric_limits<T>::max()
//  -inf  ->  std::numeric_limits<T>::lowest()
//
// Usage:
//   double val;
//   const char *end;
//   bool ok = obj::parseFloat("  +1.5e3 rest", &val, &end);
//   // val == 1500.0, end points to ' ' before "rest"
//
//   obj::ParseOptions opts;
//   opts.nan_value = -1.0;  // replace nan with -1
//   ok = obj::parseFloat("nan", &val, &end, opts);
//   // val == -1.0
//
// SPDX-License-Identifier: MIT OR Apache-2.0 OR BSL-1.0

#ifndef OBJ_PARSE_FLOAT_H_
#define OBJ_PARSE_FLOAT_H_

#include "fast_float.h"

#include <cstring>
#include <limits>

namespace obj {

template <typename T>
struct ParseOptions {
  T nan_value;
  T inf_value;
  T neg_inf_value;

  ParseOptions()
      : nan_value(static_cast<T>(0.0)),
        inf_value((std::numeric_limits<T>::max)()),
        neg_inf_value(std::numeric_limits<T>::lowest()) {}
};

namespace detail {

// Case-insensitive prefix match. Returns pointer past matched prefix, or NULL.
inline const char *match_iprefix(const char *p, const char *end,
                                 const char *prefix) {
  while (*prefix) {
    if (p == end) return NULL;
    char c = *p;
    char e = *prefix;
    // ASCII tolower without locale
    if (c >= 'A' && c <= 'Z') c += 32;
    if (e >= 'A' && e <= 'Z') e += 32;
    if (c != e) return NULL;
    ++p;
    ++prefix;
  }
  return p;
}

// Check if character is a whitespace or end-of-token in OBJ context.
inline bool is_obj_delim(char c) {
  return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\0';
}

// Try to parse nan/inf. Returns true if matched, sets *result and *end_ptr.
template <typename T>
inline bool tryParseNanInf(const char *first, const char *last, T *result,
                           const char **end_ptr,
                           const ParseOptions<T> &opts) {
  if (first >= last) return false;

  const char *p = first;
  bool negative = false;

  // Optional sign
  if (*p == '-') {
    negative = true;
    ++p;
  } else if (*p == '+') {
    ++p;
  }

  if (p >= last) return false;

  // Try "nan"
  const char *after = match_iprefix(p, last, "nan");
  if (after) {
    *result = opts.nan_value;
    *end_ptr = after;
    return true;
  }

  // Try "infinity" first (longer match), then "inf"
  after = match_iprefix(p, last, "infinity");
  if (after) {
    *result = negative ? opts.neg_inf_value : opts.inf_value;
    *end_ptr = after;
    return true;
  }

  after = match_iprefix(p, last, "inf");
  if (after) {
    *result = negative ? opts.neg_inf_value : opts.inf_value;
    *end_ptr = after;
    return true;
  }

  return false;
}

}  // namespace detail

// Parse a float/double from an OBJ token string.
//
// - Skips leading whitespace (space/tab).
// - Handles leading '+'.
// - Handles nan/inf with replacement values.
// - Sets *end_ptr to the character after the parsed number.
// - Returns true on success.
template <typename T>
inline bool parseFloat(const char *s, T *result, const char **end_ptr,
                       const ParseOptions<T> &opts = ParseOptions<T>()) {
  // Skip leading whitespace
  while (*s == ' ' || *s == '\t') ++s;

  if (*s == '\0') {
    *end_ptr = s;
    return false;
  }

  // Check first significant char to decide path.
  // nan/inf starts with [nNiI] or [+-] followed by [nNiI].
  const char *p = s;
  if (*p == '+' || *p == '-') ++p;
  char fc = *p;
  // ASCII tolower
  if (fc >= 'A' && fc <= 'Z') fc += 32;

  if (fc == 'n' || fc == 'i') {
    // Potential nan/inf — find token end and try match.
    const char *token_end = s;
    while (*token_end && !detail::is_obj_delim(*token_end)) ++token_end;
    if (s != token_end &&
        detail::tryParseNanInf(s, token_end, result, end_ptr, opts)) {
      return true;
    }
  }

  // Fast path: numeric parse (most common case).
  // Handle leading '+' which fast_float doesn't accept.
  const char *parse_start = s;
  if (*parse_start == '+') ++parse_start;

  if (*parse_start != '\0') {
    // Scan to the end of the numeric token (null or OBJ delimiter) so that
    // fast_float never reads past the bounds of the current token/buffer.
    const char *token_end = parse_start;
    while (*token_end && !detail::is_obj_delim(*token_end)) ++token_end;

    auto r = fast_float::from_chars(parse_start, token_end, *result);
    if (r.ec == std::errc()) {
      *end_ptr = r.ptr;
      return true;
    }
  }

  *end_ptr = s;
  return false;
}

// Convenience: parse from null-terminated string, no end_ptr needed.
template <typename T>
inline bool parseFloat(const char *s, T *result,
                       const ParseOptions<T> &opts = ParseOptions<T>()) {
  const char *end;
  return parseFloat(s, result, &end, opts);
}

// Parse with explicit [first, last) range (no whitespace skip, no null-term).
template <typename T>
inline bool parseFloatRange(const char *first, const char *last, T *result,
                            const char **end_ptr,
                            const ParseOptions<T> &opts = ParseOptions<T>()) {
  if (first >= last) {
    *end_ptr = first;
    return false;
  }

  // Check first significant char for nan/inf.
  const char *p = first;
  if (p < last && (*p == '+' || *p == '-')) ++p;
  if (p < last) {
    char fc = *p;
    if (fc >= 'A' && fc <= 'Z') fc += 32;
    if (fc == 'n' || fc == 'i') {
      if (detail::tryParseNanInf(first, last, result, end_ptr, opts)) {
        return true;
      }
    }
  }

  // Handle leading '+'
  const char *parse_start = first;
  if (*parse_start == '+') {
    ++parse_start;
  }

  if (parse_start >= last) {
    *end_ptr = first;
    return false;
  }

  auto r = fast_float::from_chars(parse_start, last, *result);
  if (r.ec == std::errc()) {
    *end_ptr = r.ptr;
    return true;
  }

  *end_ptr = first;
  return false;
}

}  // namespace obj

#endif  // OBJ_PARSE_FLOAT_H_
