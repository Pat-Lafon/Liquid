{-@ LIQUID "--counter-examples" @-}
{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exact-data-cons" @-}

module Intro where

import Prelude hiding (tail, concat)

{- import Language.Haskell.Liquid.Prelude  (liquidAssert) -}

class Customstk t where
    {- Ris_empty (s, 𝜈) ↦ ∀𝑢, (𝜈 =⇒ ¬mem(s, 𝑢)) ∧ (¬𝜈 ∧ hd (s, 𝑢) =⇒ mem(s, 𝑢)) -}
    {-@ is_empty :: {s:t|True} -> {u:Int|True} -> {v:Bool | v ==> not (mem s u) && (not v && (hd s == Just u ==> mem s u))} @-}
    is_empty     :: t -> Int -> Bool


    {- Rtop (s, 𝜈) ↦ ∀𝑢, mem(s, 𝜈) ∧ (𝜈 = 𝑢 ⇐⇒ hd (s, 𝑢)) -}
    {-@ top :: {s:t| True} -> {v:Int| mem s v && hd s == Just v} @-}
    top     :: t -> Int


    {- Rtail (s, 𝜈) ↦ ∀𝑢, (mem(s, 𝑢) =⇒ (mem(𝜈, 𝑢) ∨ hd (s, 𝑢)))∧
                        ((mem(𝜈, 𝑢) ∨ hd (𝜈, 𝑢)) =⇒ mem(s, 𝑢)) -}
    {-@ tail :: {s:t|True} -> {u:Int | True} -> {v:t| (mem s u ==> (mem v u || hd s == Just u)) &&
                                                        (mem v u || hd s == Just u) ==> mem s u} @-}
    tail     :: t -> Int -> t


    {- Rpush (x, s, 𝜈) ↦ ∀𝑢, (mem(𝜈, 𝑢) ∧ mem(s, 𝑢) =⇒ ¬(x = 𝑢 ∨ hd (𝜈, 𝑢)))∧
                      (mem(𝜈, 𝑢) ∧ ¬mem(s, 𝑢) =⇒ (x = 𝑢 ∧ hd (𝜈, 𝑢)))∧
                      ((x = 𝑢 ∨ hd (𝜈, 𝑢) ∨ hd (s, 𝑢) ∨ mem(s, 𝑢)) =⇒ mem(𝜈, 𝑢)) -}
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
