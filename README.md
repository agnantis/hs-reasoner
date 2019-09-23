# hs-reasoner

## Brief Description

A Haskell implementation of an OWL 2 DL Reasoner.

## Purpose

The purpose of this project is to experiment the possibilities that Functional Programming offers related to the implementation of reasoning algorithms. As most well known reasoners are written in imperative languages like _C++_ (e.g. FaCT++) or _Java_ (Hermit, Pellet), using a functional paradigm may help us develop features that are not easily implemented in using the imperative way. 

## Installation

TBA

## Implemented Features

### Supported Description Logic constructors

The hs-reasoner currently supports:

  - AL DL
    - Universal concept
    - Bottom concept
    - Atomic negation
    - Conjunction
    - Value restriction
    - Limited existential quantification
  - AL[U]
    - Disjunction
  - AL[E]
    - Full existential quantification
  - AL[C] 
    - Arbitrary negation

The hs-reasoner currently does not support:

- AL[N]
  - Number restrictions
  - Qualified number restrictions

### Optimizations

TBA
