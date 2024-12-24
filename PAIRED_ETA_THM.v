Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRED_ETA_THM_term_abbrevs.
Require Import thm52067_spec.
Require Import thm52757_spec.
Lemma lem52762 {_5264 _5271 _5272 : Type'} : term0 _5264 _5271 _5272.
Proof. exact (fun f : type1228 _5264 _5271 _5272 => @lem52067 _5264 _5271 _5272 f). Qed.
Lemma lem52763 {_5264 _5271 _5272 _5284 _5296 _5299 _5300 _5310 _5326 _5330 _5333 _5334 : Type'} : term1 _5264 _5271 _5272 _5284 _5296 _5299 _5300 _5310 _5326 _5330 _5333 _5334.
Proof. exact (conj (@lem52762 _5264 _5271 _5272) (@lem52757 _5284 _5296 _5299 _5300 _5310 _5326 _5330 _5333 _5334)). Qed.
