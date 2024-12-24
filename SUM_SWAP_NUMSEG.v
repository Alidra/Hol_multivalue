Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SWAP_NUMSEG_term_abbrevs.
Require Import FINITE_NUMSEG_spec.
Require Import SUM_SWAP_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem7221988 (m : nat) : term0 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem7221989 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7221990 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7221989 m) (@lem7221988 m)). Qed.
Lemma lem7221991 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7221990 m n). Qed.
Lemma lem7221992 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7221993 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7221992 m n) (@lem7221991 m n)). Qed.
Lemma lem7221994 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem7221996 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7221997 {A B : Type'} (f : type1416 A B) (h1 : term4 A B) : term5 A B f.
Proof. exact (@lem7221996 A B h1 f). Qed.
Lemma lem7221998 {A B : Type'} (f : type1416 A B) : (term5 A B f) = (term6 A B f).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem7221999 {A B : Type'} (f : type1416 A B) (h1 : term4 A B) : term6 A B f.
Proof. exact (EQ_MP (@lem7221998 A B f) (@lem7221997 A B f h1)). Qed.
Lemma lem7222000 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (h1 : term4 A B) : term7 A B f s.
Proof. exact (@lem7221999 A B f h1 s). Qed.
Lemma lem7222001 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term7 A B f s) = (term8 A B s f).
Proof. exact (eq_refl (term7 A B f s)). Qed.
Lemma lem7222002 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (h1 : term4 A B) : term8 A B s f.
Proof. exact (EQ_MP (@lem7222001 A B s f) (@lem7222000 A B f s h1)). Qed.
Lemma lem7222003 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (h1 : term4 A B) : term9 A B s f t.
Proof. exact (@lem7222002 A B s f h1 t). Qed.
Lemma lem7222004 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term9 A B s f t) = (term10 A B t s f).
Proof. exact (eq_refl (term9 A B s f t)). Qed.
Lemma lem7222005 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) (h1 : term4 A B) : term10 A B t s f.
Proof. exact (EQ_MP (@lem7222004 A B t s f) (@lem7222003 A B s f t h1)). Qed.
Lemma lem7222006 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term11 A B s t) : term11 A B s t.
Proof. exact (h1). Qed.
Lemma lem7222007 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B) (h2 : term11 A B s t) : (term12 A B s t f) = (term13 A B t s f).
Proof. exact (@lem7222005 A B t s f h1 (@lem7222006 A B s t h2)). Qed.
Lemma lem7222008 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term11 A B s t) : term14 A B t s f.
Proof. exact (fun h0 : term4 A B => @lem7222007 A B f s t h0 h1). Qed.
Lemma lem7222009 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7222010 {A B : Type'} (f : type1416 A B) (s : A -> Prop) (t : B -> Prop) (h1 : term4 A B) (h2 : term11 A B s t) : (term12 A B s t f) = (term13 A B t s f).
Proof. exact (@lem7222008 A B f s t h2 (@lem7222009 A B h1)). Qed.
Lemma lem7222011 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) (h1 : term4 A B) : term10 A B t s f.
Proof. exact (fun h0 : term11 A B s t => @lem7222010 A B f s t h1 h0). Qed.
Lemma lem7222012 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term4 A B) : term15 A B t s.
Proof. exact (fun f : type1416 A B => @lem7222011 A B t s f h1). Qed.
Lemma lem7222013 {A B : Type'} (t : B -> Prop) (h1 : term4 A B) : term16 A B t.
Proof. exact (fun s : A -> Prop => @lem7222012 A B t s h1). Qed.
Lemma lem7222014 {A B : Type'} (h1 : term4 A B) : term17 A B.
Proof. exact (fun t : B -> Prop => @lem7222013 A B t h1). Qed.
Lemma lem7222015 {A B : Type'} : term18 A B.
Proof. exact (fun h0 : term4 A B => @lem7222014 A B h0). Qed.
Lemma lem7222016 {A B : Type'} : term17 A B.
Proof. exact (@lem7222015 A B (@lem7124408 A B)). Qed.
Lemma lem7222017 {A B : Type'} (t : B -> Prop) : term19 A B t.
Proof. exact (@lem7222016 A B t). Qed.
Lemma lem7222018 {A B : Type'} (t : B -> Prop) : (term19 A B t) = (term16 A B t).
Proof. exact (eq_refl (term19 A B t)). Qed.
Lemma lem7222019 {A B : Type'} (t : B -> Prop) : term16 A B t.
Proof. exact (EQ_MP (@lem7222018 A B t) (@lem7222017 A B t)). Qed.
Lemma lem7222020 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term20 A B t s.
Proof. exact (@lem7222019 A B t s). Qed.
Lemma lem7222021 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term20 A B t s) = (term15 A B t s).
Proof. exact (eq_refl (term20 A B t s)). Qed.
Lemma lem7222022 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term15 A B t s.
Proof. exact (EQ_MP (@lem7222021 A B t s) (@lem7222020 A B t s)). Qed.
Lemma lem7222023 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : term21 A B t s f.
Proof. exact (@lem7222022 A B t s f). Qed.
Lemma lem7222024 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term21 A B t s f) = (term10 A B t s f).
Proof. exact (eq_refl (term21 A B t s f)). Qed.
Lemma lem7222027 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : term10 A B t s f.
Proof. exact (EQ_MP (@lem7222024 A B t s f) (@lem7222023 A B t s f)). Qed.
Lemma lem7222028 (t : nat -> Prop) (s : nat -> Prop) (f : type1607) : term22 t s f.
Proof. exact (@lem7222027 nat nat t s f). Qed.
Lemma lem7222029 (c : nat) (d : nat) (a : nat) (b : nat) (f : type1607) : term23 c d a b f.
Proof. exact (@lem7222028 (dotdot c d) (dotdot a b) f). Qed.
Lemma lem7222033 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7221994 m n) (@lem7221993 m n)). Qed.
Lemma lem7222034 (a : nat) (b : nat) : (term3 a b) = True.
Proof. exact (@lem7222033 a b). Qed.
Lemma lem7222035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7222036 (a : nat) (b : nat) : (term24 a b) = (and True).
Proof. exact (MK_COMB (@lem7222035) (@lem7222034 a b)). Qed.
Lemma lem7222038 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem7221994 m n) (@lem7221993 m n)). Qed.
Lemma lem7222039 (c : nat) (d : nat) : (term3 c d) = True.
Proof. exact (@lem7222038 c d). Qed.
Lemma lem7222040 (a : nat) (b : nat) (c : nat) (d : nat) : (term25 a b c d) = (True /\ True).
Proof. exact (MK_COMB (@lem7222036 a b) (@lem7222039 c d)). Qed.
Lemma lem7222042 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7222043 : (True /\ True) = True.
Proof. exact (@lem7222042 True). Qed.
Lemma lem7222044 (a : nat) (b : nat) (c : nat) (d : nat) : (term25 a b c d) = True.
Proof. exact (TRANS (@lem7222040 a b c d) (@lem7222043)). Qed.
Lemma lem7222045 (a : nat) (b : nat) (c : nat) (d : nat) : True = (term25 a b c d).
Proof. exact (SYM (@lem7222044 a b c d)). Qed.
Lemma lem7222046 (a : nat) (b : nat) (c : nat) (d : nat) : term25 a b c d.
Proof. exact (EQ_MP (@lem7222045 a b c d) (@lem0)). Qed.
Lemma lem7222047 (c : nat) (d : nat) (a : nat) (b : nat) (f : type1607) : (term26 a b c d f) = (term27 c d a b f).
Proof. exact (@lem7222029 c d a b f (@lem7222046 a b c d)). Qed.
Lemma lem7222052 (c : nat) (d : nat) (a : nat) (b : nat) : term28 c d a b.
Proof. exact (fun f : type1607 => @lem7222047 c d a b f). Qed.
Lemma lem7222057 (c : nat) (a : nat) (b : nat) : term29 c a b.
Proof. exact (fun d : nat => @lem7222052 c d a b). Qed.
Lemma lem7222062 (a : nat) (b : nat) : term30 a b.
Proof. exact (fun c : nat => @lem7222057 c a b). Qed.
Lemma lem7222067 (a : nat) : term31 a.
Proof. exact (fun b : nat => @lem7222062 a b). Qed.
Lemma lem7222072 : term32.
Proof. exact (fun a : nat => @lem7222067 a). Qed.
