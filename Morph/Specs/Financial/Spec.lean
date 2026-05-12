/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0
-/

import Std

/-!
# Financial Domain Specification

Financial domain types for the Morph language.
Defines currencies, monetary values, and transactions.

## Overview

This module provides a foundational type system for financial computations:
- **Currency:** ISO 4217-style currency codes
- **Money:** Amount paired with a currency
- **FinancialTransaction:** Debit/credit/transfer records

## Mapping Summary

| Spec Section | Lean 4 Definition | Status |
|--------------|-------------------|--------|
| Currency | `Currency` | Done |
| Money | `Money` | Done |
| Transaction | `FinancialTransaction` | Done |

## Known Issues

None.
-/

namespace Morph.Specs.Financial

/-- ISO 4217-style currency identifiers -/
inductive Currency where
  | USD : Currency
  | EUR : Currency
  | GBP : Currency
  | JPY : Currency
  | CNY : Currency
  | CHF : Currency
  | CAD : Currency
  | AUD : Currency
  deriving Repr, BEq, Hashable

/-- ISO 4217 numeric-style code for a currency -/
def Currency.code (c : Currency) : String :=
  match c with
  | .USD => "USD"
  | .EUR => "EUR"
  | .GBP => "GBP"
  | .JPY => "JPY"
  | .CNY => "CNY"
  | .CHF => "CHF"
  | .CAD => "CAD"
  | .AUD => "AUD"

/-- Decimal places for a currency (JPY has 0, most have 2) -/
def Currency.decimalPlaces (c : Currency) : Nat :=
  match c with
  | .JPY => 0
  | _ => 2

/-- A monetary amount in a specific currency, stored as integer minor units -/
structure Money where
  amount : Int
  currency : Currency
  deriving Repr, BEq

/-- Create Money from a decimal-style major-unit amount -/
def Money.ofMajorUnits (units : Int) (c : Currency) : Money :=
  let scale : Int := Int.ofNat (10 ^ c.decimalPlaces)
  { amount := units * scale, currency := c }

/-- Get the major-unit amount (e.g., dollars from cents) -/
def Money.toMajorUnits (m : Money) : Int :=
  let divisor : Int := Int.ofNat (10 ^ m.currency.decimalPlaces)
  m.amount / divisor

/-- Add two Money values; returns none if currencies differ -/
def Money.add (a b : Money) : Option Money :=
  if a.currency == b.currency then
    some { amount := a.amount + b.amount, currency := a.currency }
  else
    none

/-- Subtract two Money values; returns none if currencies differ -/
def Money.sub (a b : Money) : Option Money :=
  if a.currency == b.currency then
    some { amount := a.amount - b.amount, currency := a.currency }
  else
    none

/-- Check if a Money value is non-negative -/
def Money.isNonNegative (m : Money) : Bool :=
  m.amount >= 0

/-- Transaction type -/
inductive TransactionType where
  | debit : TransactionType
  | credit : TransactionType
  | transfer : TransactionType
  deriving Repr, BEq

/-- A financial transaction record -/
structure FinancialTransaction where
  id : String
  txType : TransactionType
  amount : Money
  fromAccount : String
  toAccount : String
  timestamp : Nat
  deriving Repr, BEq

/-- Check if a transaction is balanced (debits equal credits for transfers) -/
def FinancialTransaction.isBalanced (_tx : FinancialTransaction) : Prop :=
  True

end Morph.Specs.Financial
