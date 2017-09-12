# auxiliary/meta.jl
#
# A bunch of auxiliary metaprogramming tools and generated functions

import Base.tail

# OK up to N=15
_permute(t::NTuple{N,T} where {N,T}, p) = __permute((), t, p)
@inline __permute(tdst::NTuple{N,T}, tsrc::NTuple{N,T}, p) where {N,T} = tdst
@inline __permute(tdst::NTuple{N1,T}, tsrc::NTuple{N2,T}, p) where {N1,N2,T} = __permute(tuple(tdst..., tsrc[p[N1+1]]), tsrc, p)

# OK up to N=14
_memjumps(dims::Tuple{}, strides::Tuple{}) = ()
_memjumps(dims::NTuple{N,Int}, strides::NTuple{N,Int}) where {N} = tuple((dims[1]-1)*strides[1], _memjumps(tail(dims), tail(strides))...)

# inferrable and fast up to N = 14, slow afterwards
function _invperm(p::NTuple{N,T}) where {N,T<:Integer}
    ip = ntuple(n->T(n),Val{N})
    __swapsort(ip, p, 1)
end
@inline __swapsort(ip::Tuple{}, p::Tuple{}, k) = ()
@inline function __swapsort(ip::NTuple{N,Integer}, p::NTuple{N,Integer}, k) where {N}
    while p[1] != k
        p = tuple(tail(p)..., p[1])
        ip = tuple(tail(ip)..., ip[1])
    end
    tuple(ip[1], __swapsort(tail(ip), tail(p), k+1)...)
end

# Based on Tim Holy's Cartesian
function _sreplace(ex::Expr, s::Symbol, v)
    Expr(ex.head,[_sreplace(a, s, v) for a in ex.args]...)
end
_sreplace(ex::Symbol, s::Symbol, v) = ex == s ? v : ex
_sreplace(ex, s::Symbol, v) = ex

macro dividebody(N, dmax, dims, args...)
    esc(_dividebody(N, dmax, dims, args...))
end

function _dividebody(N::Int, dmax::Symbol, dims::Symbol, args...)
    mod(length(args),2)==0 || error("Wrong number of arguments")
    argiter = 1:2:length(args)-2

    ex = Expr(:block)
    newdims = gensym(:newdims)
    newdim = gensym(:newdim)
    mainex1 = _sreplace(args[end-1], dims, newdims)
    mainex2 = _sreplace(args[end], dims, newdims)

    for d = 1:N
        updateex = Expr(:block,[:($(args[i]) += $newdim*$(args[i+1]).strides[$d]) for i in argiter]...)
        newdimsex = Expr(:tuple,[Expr(:ref,dims,i) for i=1:d-1]..., newdim, [Expr(:ref,dims,i) for i=d+1:N]...)
        body = quote
            $newdim = $dims[$d] >> 1
            $newdims = $newdimsex
            $mainex1
            $updateex
            $newdim = $dims[$d] - $newdim
            $newdims = $newdimsex
            $mainex2
        end
        ex = Expr(:if,:($dmax == $d), body,ex)
    end
    ex
end

macro stridedloops(N, dims, args...)
    esc(_stridedloops(N, dims, args...))
end
function _stridedloops(N::Int, dims::Symbol, args...)
    mod(length(args),3)==1 || error("Wrong number of arguments")
    argiter = 1:3:length(args)-1
    body = args[end]
    pre = [Expr(:(=), args[i], Symbol(args[i],0)) for i in argiter]
    ex = Expr(:block, pre..., body)
    for d = 1:N
        pre = [Expr(:(=), Symbol(args[i], d-1), Symbol(args[i], d)) for i in argiter]
        post = [Expr(:(+=), Symbol(args[i], d), Expr(:ref, args[i+2], d)) for i in argiter]
        ex = Expr(:block, pre..., ex, post...)
        rangeex = Expr(:(:), 1, Expr(:ref, dims, d))
        forex = Expr(:(=), gensym(), rangeex)
        ex = Expr(:for, forex, ex)
        if d==1
            if VERSION < v"0.7-"
                ex = Expr(:macrocall, Symbol("@simd"), ex)
            else
                ex = Expr(:macrocall, Symbol("@simd"), LineNumberNode(@__LINE__), ex)
            end
        end
    end
    pre = [Expr(:(=),Symbol(args[i],N),args[i+1]) for i in argiter]
    ex = Expr(:block, pre..., ex)
    return ex
end
