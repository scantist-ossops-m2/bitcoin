// Copyright (c) 2018-2019 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_UTIL_SPANPARSING_H
#define BITCOIN_UTIL_SPANPARSING_H

#include <span.h>

#include <string>
#include <vector>

namespace spanparsing {

/** Parse a constant.
 *
 * If sp's initial part matches str, sp is updated to skip that part, and true is returned.
 * Otherwise sp is unmodified and false is returned.
 */
bool Const(const std::string& str, Span<const char>& sp);

/** Parse a function call.
 *
 * If sp's initial part matches str + "(", and sp ends with ")", sp is updated to be the
 * section between the braces, and true is returned. Otherwise sp is unmodified and false
 * is returned.
 */
bool Func(const std::string& str, Span<const char>& sp);

/** Extract the expression that sp begins with.
 *
 * This function will return the initial part of sp, up to (but not including) the first
 * comma or closing brace, skipping ones that are surrounded by braces. So for example,
 * for "foo(bar(1),2),3" the initial part "foo(bar(1),2)" will be returned. sp will be
 * updated to skip the initial part that is returned.
 */
Span<const char> Expr(Span<const char>& sp);

/** Split a string on every instance of sep, returning a vector.
 *
 * If sep does not occur in sp, a singleton with the entirety of sp is returned.
 *
 * Note that this function does not care about braces, so splitting
 * "foo(bar(1),2),3) on ',' will return {"foo(bar(1)", "2)", "3)"}.
 */
std::vector<Span<const char>> Split(const Span<const char>& sp, char sep);

} // namespace spanparsing

namespace genspanparsing {

struct NoValue {};

template<typename In, typename Out> using Parser = std::function<std::function<void()>(Span<const In>, std::function<void(std::optional<Out>)>)>;

namespace detail {


} // namespace genspanparsing::detail

template<typename In, typename Out> std::optional<Out> Parse(Parser<In,Out> parser, Span<const In> input)
{
    std::optional<Out> ret;
    std::function<void()> todo = [input,&parser](){parser(input, [&ret](std::optional<Out> res){ ret = std::move(res); });}
    while (todo) {
        todo = todo();
    }
    return ret;
}

template<typename In> 
Parser<In, NoValue> Const(Span<const In> cte) {
    return [cte](Span<const In> arg, std::function<void(std::optional<NoValue>)> cb){
        if (arg.size() < cte.size() || arg.subspan(0, cte.size()) != cte) {
            return [cb=std::move(cb)](){cb(std::nullopt);};
        } else {
            return [cb=std::move(cb)](){cb(NoValue{});};
        }
    };
}

template<typename In, typename Out>
Parser<In, std::vector<Out>> Repeat(Parser<In, Out> parser, Span<const In> sep){
    return [parser=std::move(parser),sep](Span<const In> arg, std::function<void(std::optional<NoValue>)> cb){
        
    }
}

} // namespace genspanparsing

#endif // BITCOIN_UTIL_SPANPARSING_H
