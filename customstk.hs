{-@ LIQUID "--counter-examples" @-}
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Intro where

import Prelude hiding (tail, concat)

{- import Language.Haskell.Liquid.Prelude  (liquidAssert) -}

class Customstk t where
    {- Ris_empty (s, π) β¦ βπ’, (π =β Β¬mem(s, π’)) β§ (Β¬π β§ hd (s, π’) =β mem(s, π’)) -}
    {-@ is_empty :: {s:t|True} -> {u:Int|True} -> {v:Bool | v ==> not (mem s u) && (not v && (hd s == Just u ==> mem s u))} @-}
    is_empty     :: t -> Int -> Bool


    {- Rtop (s, π) β¦ βπ’, mem(s, π) β§ (π = π’ ββ hd (s, π’)) -}
    {-@ top :: {s:t| True} -> {v:Int| mem s v && hd s == Just v} @-}
    top     :: t -> Int


    {- Rtail (s, π) β¦ βπ’, (mem(s, π’) =β (mem(π, π’) β¨ hd (s, π’)))β§
                        ((mem(π, π’) β¨ hd (π, π’)) =β mem(s, π’)) -}
    {-@ tail :: {s:t|True} -> {u:Int | True} -> {v:t| (mem s u ==> (mem v u || hd s == Just u)) &&
                                                        (mem v u || hd s == Just u) ==> mem s u} @-}
    tail     :: t -> Int -> t


    {- Rpush (x, s, π) β¦ βπ’, (mem(π, π’) β§ mem(s, π’) =β Β¬(x = π’ β¨ hd (π, π’)))β§
                      (mem(π, π’) β§ Β¬mem(s, π’) =β (x = π’ β§ hd (π, π’)))β§
                      ((x = π’ β¨ hd (π, π’) β¨ hd (s, π’) β¨ mem(s, π’)) =β mem(π, π’)) -}
    {-@ push :: {x:Int| True} -> {s:t| True} -> {u: Int | True} -> {v:t| ((mem v u && mem s u) ==> (x != u || hd v == Just u)) && ((mem v u && not (mem s u)) ==> (x == u && hd v == Just u)) && ((x == u || hd v == Just u || hd s == Just u || mem s u) ==> mem v u)} @-}
    push     :: Int -> t -> Int -> t


{-@ measure hd :: (Customstk t) => t -> Maybe Int @-}
{-@ measure mem :: (Customstk t) => t -> Int -> Bool @-}

{- {-@ reflect mem @-}
mem :: (Customstk t) => t -> Int -> (t -> Bool) -> (t -> Int) -> (t -> t) -> Bool
mem s u is_empty top tail = if is_empty s then False else (top s == u) || mem (tail s) u is_empty top tail -}


{-@ concat :: {s1:t | True} -> {s2:t | True} -> {n : Int | True} -> {s:t | (hd s == hd s1 || hd s == hd s2) && (mem s n <=> (mem s1 n || mem s2 n))} @-}
concat :: (Customstk t) => t -> t -> Int -> t
concat s1 s2 n =
  if is_empty s1 n then s2
  else push (top s1) (concat (tail s1 n) s2 n) n
