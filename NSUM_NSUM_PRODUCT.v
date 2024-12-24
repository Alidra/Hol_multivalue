Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_NSUM_PRODUCT_term_abbrevs.
Require Import ITERATE_ITERATE_PRODUCT_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7017951 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7017953 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7017954 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7017953 A B C h1 op). Qed.
Lemma lem7017955 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7017956 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7017955 A B C op) (@lem7017954 A B C op h1)). Qed.
Lemma lem7017957 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7017958 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7017956 A B C op h1 (@lem7017957 C op h2)). Qed.
Lemma lem7017959 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7017958 A B C op h0 h1). Qed.
Lemma lem7017960 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7017961 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7017959 A B C op h2 (@lem7017960 A B C h1)). Qed.
Lemma lem7017962 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7017961 A B C op h1 h0). Qed.
Lemma lem7017963 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7017962 A B C op h1). Qed.
Lemma lem7017964 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7017963 A B C h0). Qed.
Lemma lem7017965 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7017964 A B C (@lem5970042 A B C)). Qed.
Lemma lem7017966 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7017965 A B C op). Qed.
Lemma lem7017967 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7017994 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7017995 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7017994 A). Qed.
Lemma lem7017996 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7017997 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7017995 A) (@lem7017996 A s)). Qed.
Lemma lem7017999 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018000 {B : Type'} : (@nsum B) = (@iterate nat B Nat.add).
Proof. exact (@lem7017999 B). Qed.
Lemma lem7018001 {A B : Type'} (t : type1413 A B) (i : A) : (t i) = (t i).
Proof. exact (eq_refl (t i)). Qed.
Lemma lem7018002 {A B : Type'} (t : type1413 A B) (i : A) : (term6 A B t i) = (term7 A B t i).
Proof. exact (MK_COMB (@lem7018000 B) (@lem7018001 A B t i)). Qed.
Lemma lem7018003 {A B : Type'} (x : type1415 A B) (i : A) : (x i) = (x i).
Proof. exact (eq_refl (x i)). Qed.
Lemma lem7018004 {A B : Type'} (t : type1413 A B) (x : type1415 A B) (i : A) : (term8 A B t x i) = (term9 A B t x i).
Proof. exact (MK_COMB (@lem7018002 A B t i) (@lem7018003 A B x i)). Qed.
Lemma lem7018005 {A B : Type'} (t : type1413 A B) (x : type1415 A B) : (term10 A B t x) = (term11 A B t x).
Proof. exact (fun_ext (fun i : A => @lem7018004 A B t x i)). Qed.
Lemma lem7018006 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1415 A B) : (term12 A B s t x) = (term13 A B s t x).
Proof. exact (MK_COMB (@lem7017997 A s) (@lem7018005 A B t x)). Qed.
Lemma lem7018007 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018008 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1415 A B) : (term14 A B s t x) = (term15 A B s t x).
Proof. exact (MK_COMB (@lem7018007) (@lem7018006 A B s t x)). Qed.
Lemma lem7018010 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018011 {A B : Type'} : (@nsum (prod A B)) = (@iterate nat (prod A B) Nat.add).
Proof. exact (@lem7018010 (prod A B)). Qed.
Lemma lem7018022 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term16 A B s t) = (term16 A B s t).
Proof. exact (eq_refl (term16 A B s t)). Qed.
Lemma lem7018023 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term17 A B s t) = (term18 A B s t).
Proof. exact (MK_COMB (@lem7018011 A B) (@lem7018022 A B s t)). Qed.
Lemma lem7018032 {A B : Type'} (x : type1415 A B) : (term19 A B x) = (term19 A B x).
Proof. exact (eq_refl (term19 A B x)). Qed.
Lemma lem7018033 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1415 A B) : (term20 A B s t x) = (term21 A B s t x).
Proof. exact (MK_COMB (@lem7018023 A B s t) (@lem7018032 A B x)). Qed.
Lemma lem7018034 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1415 A B) : ((term12 A B s t x) = (term20 A B s t x)) = ((term13 A B s t x) = (term21 A B s t x)).
Proof. exact (MK_COMB (@lem7018008 A B s t x) (@lem7018033 A B s t x)). Qed.
Lemma lem7018037 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term22 A B s t) = (term22 A B s t).
Proof. exact (eq_refl (term22 A B s t)). Qed.
Lemma lem7018038 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : type1415 A B) : (term23 A B s t x) = (term24 A B s t x).
Proof. exact (MK_COMB (@lem7018037 A B s t) (@lem7018034 A B s t x)). Qed.
Lemma lem7018041 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term25 A B s t) = (term26 A B s t).
Proof. exact (fun_ext (fun x : type1415 A B => @lem7018038 A B s t x)). Qed.
Lemma lem7018042 {A B : Type'} : (@all (A -> B -> nat)) = (@all (A -> B -> nat)).
Proof. exact (eq_refl (@all (A -> B -> nat))). Qed.
Lemma lem7018043 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term27 A B s t) = (term28 A B s t).
Proof. exact (MK_COMB (@lem7018042 A B) (@lem7018041 A B s t)). Qed.
Lemma lem7018048 {A B : Type'} (s : A -> Prop) : (term29 A B s) = (term30 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem7018043 A B s t)). Qed.
Lemma lem7018049 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem7018050 {A B : Type'} (s : A -> Prop) : (term31 A B s) = (term32 A B s).
Proof. exact (MK_COMB (@lem7018049 A B) (@lem7018048 A B s)). Qed.
Lemma lem7018055 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7018050 A B s)). Qed.
Lemma lem7018056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018057 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem7018056 A) (@lem7018055 A B)). Qed.
Lemma lem7018062 {A B : Type'} : (term36 A B) = (term35 A B).
Proof. exact (SYM (@lem7018057 A B)). Qed.
Lemma lem7018064 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7017967 A B C op) (@lem7017966 A B C op)). Qed.
Lemma lem7018065 {A B : Type'} (op : type1606) : term37 A B op.
Proof. exact (@lem7018064 A B nat op). Qed.
Lemma lem7018066 {A B : Type'} : term38 A B.
Proof. exact (@lem7018065 A B Nat.add). Qed.
Lemma lem7018068 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7017951) (@lem6924403)). Qed.
Lemma lem7018069 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7018068)). Qed.
Lemma lem7018070 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7018069) (@lem0)). Qed.
Lemma lem7018071 {A B : Type'} : term36 A B.
Proof. exact (@lem7018066 A B (@lem7018070)). Qed.
Lemma lem7018072 {A B : Type'} : term35 A B.
Proof. exact (EQ_MP (@lem7018062 A B) (@lem7018071 A B)). Qed.
