Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import iterate_term_abbrevs.
Lemma lem5717966 {_119779 A : Type'} : (@iterate _119779 A) = (term0 _119779 A).
Proof. exact (@iterate_def _119779 A). Qed.
Lemma lem5717967 {_119779 : Type'} (_71715 : type1400 _119779) : _71715 = _71715.
Proof. exact (eq_refl _71715). Qed.
Lemma lem5717968 {_119779 A : Type'} (_71715 : type1400 _119779) : (@iterate _119779 A _71715) = (term1 _119779 A _71715).
Proof. exact (MK_COMB (@lem5717966 _119779 A) (@lem5717967 _119779 _71715)). Qed.
Lemma lem5717969 {_119779 A : Type'} (_71715 : type1400 _119779) : (term1 _119779 A _71715) = (term2 _119779 A _71715).
Proof. exact (eq_refl (term1 _119779 A _71715)). Qed.
Lemma lem5717970 {_119779 A : Type'} (_71715 : type1400 _119779) : (@iterate _119779 A _71715) = (term2 _119779 A _71715).
Proof. exact (TRANS (@lem5717968 _119779 A _71715) (@lem5717969 _119779 A _71715)). Qed.
Lemma lem5717971 {A : Type'} (_71716 : A -> Prop) : _71716 = _71716.
Proof. exact (eq_refl _71716). Qed.
Lemma lem5717972 {_119779 A : Type'} (_71715 : type1400 _119779) (_71716 : A -> Prop) : (@iterate _119779 A _71715 _71716) = (term3 _119779 A _71715 _71716).
Proof. exact (MK_COMB (@lem5717970 _119779 A _71715) (@lem5717971 A _71716)). Qed.
Lemma lem5717973 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) : (term3 _119779 A _71715 _71716) = (term4 _119779 A _71716 _71715).
Proof. exact (eq_refl (term3 _119779 A _71715 _71716)). Qed.
Lemma lem5717974 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) : (@iterate _119779 A _71715 _71716) = (term4 _119779 A _71716 _71715).
Proof. exact (TRANS (@lem5717972 _119779 A _71715 _71716) (@lem5717973 _119779 A _71716 _71715)). Qed.
Lemma lem5717975 {_119779 A : Type'} (_71717 : A -> _119779) : _71717 = _71717.
Proof. exact (eq_refl _71717). Qed.
Lemma lem5717976 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) (_71717 : A -> _119779) : (@iterate _119779 A _71715 _71716 _71717) = (term5 _119779 A _71716 _71715 _71717).
Proof. exact (MK_COMB (@lem5717974 _119779 A _71716 _71715) (@lem5717975 _119779 A _71717)). Qed.
Lemma lem5717977 {_119779 A : Type'} (_71717 : A -> _119779) (_71716 : A -> Prop) (_71715 : type1400 _119779) : (term5 _119779 A _71716 _71715 _71717) = (term6 _119779 A _71717 _71716 _71715).
Proof. exact (eq_refl (term5 _119779 A _71716 _71715 _71717)). Qed.
Lemma lem5717978 {_119779 A : Type'} (_71717 : A -> _119779) (_71716 : A -> Prop) (_71715 : type1400 _119779) : (@iterate _119779 A _71715 _71716 _71717) = (term6 _119779 A _71717 _71716 _71715).
Proof. exact (TRANS (@lem5717976 _119779 A _71716 _71715 _71717) (@lem5717977 _119779 A _71717 _71716 _71715)). Qed.
Lemma lem5717979 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) : term7 _119779 A _71716 _71715.
Proof. exact (fun _71717 : A -> _119779 => @lem5717978 _119779 A _71717 _71716 _71715). Qed.
Lemma lem5717980 {_119779 A : Type'} (_71715 : type1400 _119779) : term8 _119779 A _71715.
Proof. exact (fun _71716 : A -> Prop => @lem5717979 _119779 A _71716 _71715). Qed.
Lemma lem5717981 {_119779 A : Type'} : term9 _119779 A.
Proof. exact (fun _71715 : type1400 _119779 => @lem5717980 _119779 A _71715). Qed.
Lemma lem5717982 {_119779 A : Type'} (_71715 : type1400 _119779) : term10 _119779 A _71715.
Proof. exact (@lem5717981 _119779 A _71715). Qed.
Lemma lem5717983 {_119779 A : Type'} (_71715 : type1400 _119779) : (term10 _119779 A _71715) = (term8 _119779 A _71715).
Proof. exact (eq_refl (term10 _119779 A _71715)). Qed.
Lemma lem5717984 {_119779 A : Type'} (_71715 : type1400 _119779) : term8 _119779 A _71715.
Proof. exact (EQ_MP (@lem5717983 _119779 A _71715) (@lem5717982 _119779 A _71715)). Qed.
Lemma lem5717985 {_119779 A : Type'} (_71715 : type1400 _119779) (_71716 : A -> Prop) : term11 _119779 A _71715 _71716.
Proof. exact (@lem5717984 _119779 A _71715 _71716). Qed.
Lemma lem5717986 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) : (term11 _119779 A _71715 _71716) = (term7 _119779 A _71716 _71715).
Proof. exact (eq_refl (term11 _119779 A _71715 _71716)). Qed.
Lemma lem5717987 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) : term7 _119779 A _71716 _71715.
Proof. exact (EQ_MP (@lem5717986 _119779 A _71716 _71715) (@lem5717985 _119779 A _71715 _71716)). Qed.
Lemma lem5717988 {_119779 A : Type'} (_71716 : A -> Prop) (_71715 : type1400 _119779) (_71717 : A -> _119779) : term12 _119779 A _71716 _71715 _71717.
Proof. exact (@lem5717987 _119779 A _71716 _71715 _71717). Qed.
Lemma lem5717989 {_119779 A : Type'} (_71717 : A -> _119779) (_71716 : A -> Prop) (_71715 : type1400 _119779) : (term12 _119779 A _71716 _71715 _71717) = ((@iterate _119779 A _71715 _71716 _71717) = (term6 _119779 A _71717 _71716 _71715)).
Proof. exact (eq_refl (term12 _119779 A _71716 _71715 _71717)). Qed.
Lemma lem5717990 {_119779 A : Type'} (_71717 : A -> _119779) (_71716 : A -> Prop) (_71715 : type1400 _119779) : (@iterate _119779 A _71715 _71716 _71717) = (term6 _119779 A _71717 _71716 _71715).
Proof. exact (EQ_MP (@lem5717989 _119779 A _71717 _71716 _71715) (@lem5717988 _119779 A _71716 _71715 _71717)). Qed.
Lemma lem5718046 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) (op : type1400 _119779) : (@iterate _119779 A op s f) = (term6 _119779 A f s op).
Proof. exact (@lem5717990 _119779 A f s op). Qed.
Lemma lem5718047 {_119779 A : Type'} (f : A -> _119779) (s : A -> Prop) : term13 _119779 A f s.
Proof. exact (fun op : type1400 _119779 => @lem5718046 _119779 A f s op). Qed.
Lemma lem5718048 {_119779 A : Type'} (f : A -> _119779) : term14 _119779 A f.
Proof. exact (fun s : A -> Prop => @lem5718047 _119779 A f s). Qed.
Lemma lem5718049 {_119779 A : Type'} : term15 _119779 A.
Proof. exact (fun f : A -> _119779 => @lem5718048 _119779 A f). Qed.
