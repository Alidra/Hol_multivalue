Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SETSPEC_term_abbrevs.
Lemma lem3182965 {_83031 : Type'} : (@SETSPEC _83031) = (term0 _83031).
Proof. exact (@SETSPEC_def _83031). Qed.
Lemma lem3182966 {_83031 : Type'} (_32700 : _83031) : _32700 = _32700.
Proof. exact (eq_refl _32700). Qed.
Lemma lem3182967 {_83031 : Type'} (_32700 : _83031) : (@SETSPEC _83031 _32700) = (term1 _83031 _32700).
Proof. exact (MK_COMB (@lem3182965 _83031) (@lem3182966 _83031 _32700)). Qed.
Lemma lem3182968 {_83031 : Type'} (_32700 : _83031) : (term1 _83031 _32700) = (term2 _83031 _32700).
Proof. exact (eq_refl (term1 _83031 _32700)). Qed.
Lemma lem3182969 {_83031 : Type'} (_32700 : _83031) : (@SETSPEC _83031 _32700) = (term2 _83031 _32700).
Proof. exact (TRANS (@lem3182967 _83031 _32700) (@lem3182968 _83031 _32700)). Qed.
Lemma lem3182970 (_32701 : Prop) : _32701 = _32701.
Proof. exact (eq_refl _32701). Qed.
Lemma lem3182971 {_83031 : Type'} (_32700 : _83031) (_32701 : Prop) : (@SETSPEC _83031 _32700 _32701) = (term3 _83031 _32700 _32701).
Proof. exact (MK_COMB (@lem3182969 _83031 _32700) (@lem3182970 _32701)). Qed.
Lemma lem3182972 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) : (term3 _83031 _32700 _32701) = (term4 _83031 _32701 _32700).
Proof. exact (eq_refl (term3 _83031 _32700 _32701)). Qed.
Lemma lem3182973 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) : (@SETSPEC _83031 _32700 _32701) = (term4 _83031 _32701 _32700).
Proof. exact (TRANS (@lem3182971 _83031 _32700 _32701) (@lem3182972 _83031 _32701 _32700)). Qed.
Lemma lem3182974 {_83031 : Type'} (_32702 : _83031) : _32702 = _32702.
Proof. exact (eq_refl _32702). Qed.
Lemma lem3182975 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : (@SETSPEC _83031 _32700 _32701 _32702) = (term5 _83031 _32701 _32700 _32702).
Proof. exact (MK_COMB (@lem3182973 _83031 _32701 _32700) (@lem3182974 _83031 _32702)). Qed.
Lemma lem3182976 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : (term5 _83031 _32701 _32700 _32702) = (term6 _83031 _32701 _32700 _32702).
Proof. exact (eq_refl (term5 _83031 _32701 _32700 _32702)). Qed.
Lemma lem3182977 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : (@SETSPEC _83031 _32700 _32701 _32702) = (term6 _83031 _32701 _32700 _32702).
Proof. exact (TRANS (@lem3182975 _83031 _32701 _32700 _32702) (@lem3182976 _83031 _32701 _32700 _32702)). Qed.
Lemma lem3182978 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) : term7 _83031 _32701 _32700.
Proof. exact (fun _32702 : _83031 => @lem3182977 _83031 _32701 _32700 _32702). Qed.
Lemma lem3182979 {_83031 : Type'} (_32700 : _83031) : term8 _83031 _32700.
Proof. exact (fun _32701 : Prop => @lem3182978 _83031 _32701 _32700). Qed.
Lemma lem3182980 {_83031 : Type'} : term9 _83031.
Proof. exact (fun _32700 : _83031 => @lem3182979 _83031 _32700). Qed.
Lemma lem3182981 {_83031 : Type'} (_32700 : _83031) : term10 _83031 _32700.
Proof. exact (@lem3182980 _83031 _32700). Qed.
Lemma lem3182982 {_83031 : Type'} (_32700 : _83031) : (term10 _83031 _32700) = (term8 _83031 _32700).
Proof. exact (eq_refl (term10 _83031 _32700)). Qed.
Lemma lem3182983 {_83031 : Type'} (_32700 : _83031) : term8 _83031 _32700.
Proof. exact (EQ_MP (@lem3182982 _83031 _32700) (@lem3182981 _83031 _32700)). Qed.
Lemma lem3182984 {_83031 : Type'} (_32700 : _83031) (_32701 : Prop) : term11 _83031 _32700 _32701.
Proof. exact (@lem3182983 _83031 _32700 _32701). Qed.
Lemma lem3182985 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) : (term11 _83031 _32700 _32701) = (term7 _83031 _32701 _32700).
Proof. exact (eq_refl (term11 _83031 _32700 _32701)). Qed.
Lemma lem3182986 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) : term7 _83031 _32701 _32700.
Proof. exact (EQ_MP (@lem3182985 _83031 _32701 _32700) (@lem3182984 _83031 _32700 _32701)). Qed.
Lemma lem3182987 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : term12 _83031 _32701 _32700 _32702.
Proof. exact (@lem3182986 _83031 _32701 _32700 _32702). Qed.
Lemma lem3182988 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : (term12 _83031 _32701 _32700 _32702) = ((@SETSPEC _83031 _32700 _32701 _32702) = (term6 _83031 _32701 _32700 _32702)).
Proof. exact (eq_refl (term12 _83031 _32701 _32700 _32702)). Qed.
Lemma lem3182989 {_83031 : Type'} (_32701 : Prop) (_32700 : _83031) (_32702 : _83031) : (@SETSPEC _83031 _32700 _32701 _32702) = (term6 _83031 _32701 _32700 _32702).
Proof. exact (EQ_MP (@lem3182988 _83031 _32701 _32700 _32702) (@lem3182987 _83031 _32701 _32700 _32702)). Qed.
Lemma lem3183045 {_83031 : Type'} (P : Prop) (v : _83031) (t : _83031) : (@SETSPEC _83031 v P t) = (term6 _83031 P v t).
Proof. exact (@lem3182989 _83031 P v t). Qed.
Lemma lem3183046 {_83031 : Type'} (P : Prop) (v : _83031) : term7 _83031 P v.
Proof. exact (fun t : _83031 => @lem3183045 _83031 P v t). Qed.
Lemma lem3183047 {_83031 : Type'} (P : Prop) : term13 _83031 P.
Proof. exact (fun v : _83031 => @lem3183046 _83031 P v). Qed.
Lemma lem3183048 {_83031 : Type'} : term14 _83031.
Proof. exact (fun P : Prop => @lem3183047 _83031 P). Qed.
