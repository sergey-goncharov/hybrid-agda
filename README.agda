------------------------------------------------------------------------
-- Code related to the paper "Towards Constructive Hybrid Semantics"
--
-- Tim Lukas Diezel and Sergey Goncharov
------------------------------------------------------------------------

{-# OPTIONS --cubical --safe #-}

module README where

import Sets
import Functor
import Kleisli
import ElgotIteration
import PartialOrder
import CompletePartialOrder
import DecidableOrder
import Monoid
import MonoidModule
import Eliminators-L-wave
import Eliminators-L-bar
import DurationMonad-L-wave
import DurationMonad-L-bar
import ChainCompletion
import Cantor

------------------------------------------------------------------------
-- Section 2: Preliminaries

-- Ordered monoids
O-Monoid = Monoid.O-Monoid

-- Free objects
FreeObject = Functor.FreeObject

-- Monads in the form of Kleisli triples
Monad = Kleisli.Kleisli

-- Elgot iteration
ElgotIteration = ElgotIteration.TotalUniConway

------------------------------------------------------------------------
-- Section 3: Hybrid Semantics and Beyond

-- Monoid modules
MonoidModule = MonoidModule.M-Module

------------------------------------------------------------------------
-- Section 4: Complete Monoid Modules, Categorically

-- Complete 𝕄-modules
CompleteMonoidModule = MonoidModule.Complete-OM-Module

-- Free complete 𝕄-module
Free-Complete-𝕄-module = MonoidModule.Initial-Complete-OM-Module-over

-- Theorem 7
-- 1.

-- Existence of all free objects yields a monad
FreeObjects→Monad = Kleisli.FreeObj→Kleisli

-- L̃ forms a monad
DurationMonad-L̃ = DurationMonad-L-wave.L̃-DurationMonad

-- 2.

-- Kleisli composition is strict on both sides
LeftMonotonicity-L̃ = DurationMonad-L-wave.*-monoˡ
RightMonotonicity-L̃ = DurationMonad-L-wave.*-monoʳ
LeftContinuity-L̃ = DurationMonad-L-wave.*-contˡ
RightContinuity-L̃ = DurationMonad-L-wave.*-contʳ

-- 3.

-- Iteration operator † on L̃ calculated as a least fixed point
Iteration-L̃ = DurationMonad-L-wave.L̃-Iteration

-- † satisfies the iteration laws
IterationLaws-L̃ = DurationMonad-L-wave.L̃-UniConway

------------------------------------------------------------------------
-- Section 5: Complete Monoid Modules, Classically

-- Two equivalent formulations of the axiom of countable choice
ACω = Sets.ACω
ACω′ = Sets.ACω′

-- Directed chains
-- (intensional)
DirectedChain = PartialOrder.DirSeq
-- (extensional)
‖DirectedChain‖ = PartialOrder.‖DirSeq‖

-- Directed-complete sets
-- (intensional)
DirectedCompleteSet = CompletePartialOrder.D-CompletePartialOrder
-- (extensional)
‖DirectedCompleteSet‖ = CompletePartialOrder.‖D-CompletePartialOrder‖

-- Chain completion
ChainCompletion = ChainCompletion.Ã

-- Cantor pairing function
Cantor = Cantor.π

------------------------------------------------------------------------
-- Section 6: Conservatively Complete Monoid Modules

-- Conservatively complete 𝕄-modules
Conservatively-Complete-𝕄-Module = MonoidModule.C-Complete-OM-Module

-- Theorem 19
-- 1.

-- L̅ forms a monad
DurationMonad-L̅ = DurationMonad-L-bar.L̅-DurationMonad

-- 2.

-- Kleisli composition is strict on both sides
LeftMonotonicity-L̅ = DurationMonad-L-bar.*-monoˡ
RightMonotonicity-L̅ = DurationMonad-L-bar.*-monoʳ
LeftContinuity-L̅ = DurationMonad-L-bar.*-contˡ
RightContinuity-L̅ = DurationMonad-L-bar.*-contʳ

-- 3.

-- Iteration operator † on L̅ calculated as a least fixed point
Iteration-L̅ = DurationMonad-L-bar.L̃-Iteration

-- † satisfies the iteration laws
IterationLaws-L̅ = DurationMonad-L-bar.L̃-UniConway

------------------------------------------------------------------------
-- Section 7: Formalization in HoTT/Cubical Agda

-- The property of being a (mere) proposition
IsProp = Sets.IsProp

-- The property of being a set
IsSet = Sets.IsSet

-- Propositional Truncation
‖_‖ = Sets.‖_‖

-- Increasingness
IsIncreasing = PartialOrder.Inc

-- Intensional Directedness
IsDirected = PartialOrder.Dir

-- Extensional Directedness
Is‖Directed‖ = PartialOrder.‖Dir‖

-- Proposition 21
-- (a) ⇒ (b)
a⇒b = CompletePartialOrder.‖DCPO‖→DCPO

-- (b) ⇒ (c)
b⇒c = CompletePartialOrder.DCPO→ωCPO

-- (b) ⇒ (a)
b⇒a = CompletePartialOrder.DCPO→‖DCPO‖

-- (c) ⇒ (a)
c⇒a = DecidableOrder.ωCPO→‖DCPO‖
HoTT-Exercise-3-19 = DecidableOrder.restore-ωC

-- The HIIT L̃
L̃ = Eliminators-L-wave.Def-L̃.L̃

-- The HIIT L̅
L̅ = Eliminators-L-bar.Def-L̅.L̅

-- Diagonalization argument for Dir-completeness
dseq-dseq→dseq = PartialOrder.dseq-dseq→dseq
