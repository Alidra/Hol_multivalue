Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7933086_term_abbrevs.
Require Import HAS_SIZE_1_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7603427_spec.
Require Import thm7637206_spec.
Require Import thm7640378_spec.
Require Import thm7640410_spec.
Require Import thm7640437_spec.
Require Import thm7932275_spec.
Require Import thm7932276_spec.
Require Import thm7932281_spec.
Require Import thm7932282_spec.
Require Import thm7932286_spec.
Require Import thm7932287_spec.
Require Import thm7932316_spec.
Require Import thm7932317_spec.
Require Import thm7932405_spec.
Require Import thm7932948_spec.
Lemma lem7932950 {A B : Type'} (f : A -> B) (s : A -> Prop) (n : nat) : term0 A B f s n.
Proof. exact (EQ_MP (@lem7932317 A B f s n) (@lem7932316 A B f s n)). Qed.
Lemma lem7932951 {A : Type'} (f : type40 A) (s : type42 A) (n : nat) : term1 A f s n.
Proof. exact (@lem7932950 (type6 A) (tybit1 A) f s n). Qed.
Lemma lem7932952 {A : Type'} : term2 A.
Proof. exact (@lem7932951 A (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)) (term3 A)). Qed.
Lemma lem7932968 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7932287 A x) (@lem7932286 A x)). Qed.
Lemma lem7932969 {A : Type'} (x : type6 A) : (@IN (finite_sum (finite_sum A A) unit) x (@UNIV (finite_sum (finite_sum A A) unit))) = True.
Proof. exact (@lem7932968 (type6 A) x). Qed.
Lemma lem7932970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932971 {A : Type'} (x : type6 A) : (term4 A x) = (and True).
Proof. exact (MK_COMB (@lem7932970) (@lem7932969 A x)). Qed.
Lemma lem7932975 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7932287 A x) (@lem7932286 A x)). Qed.
Lemma lem7932976 {A : Type'} (x : type6 A) : (@IN (finite_sum (finite_sum A A) unit) x (@UNIV (finite_sum (finite_sum A A) unit))) = True.
Proof. exact (@lem7932975 (type6 A) x). Qed.
Lemma lem7932977 {A : Type'} (y : type6 A) : (@IN (finite_sum (finite_sum A A) unit) y (@UNIV (finite_sum (finite_sum A A) unit))) = True.
Proof. exact (@lem7932976 A y). Qed.
Lemma lem7932978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932979 {A : Type'} (y : type6 A) : (term4 A y) = (and True).
Proof. exact (MK_COMB (@lem7932978) (@lem7932977 A y)). Qed.
Lemma lem7932981 {A : Type'} (a : type6 A) (a' : type6 A) : ((@mktybit1 A a) = (@mktybit1 A a')) = (a = a').
Proof. exact (EQ_MP (@lem7932282 A a a') (@lem7932281 A a a')). Qed.
Lemma lem7932982 {A : Type'} (a : type6 A) (a' : type6 A) : ((@mktybit1 A a) = (@mktybit1 A a')) = (a = a').
Proof. exact (@lem7932981 A a a'). Qed.
Lemma lem7932983 {A : Type'} (x : type6 A) (y : type6 A) : ((@mktybit1 A x) = (@mktybit1 A y)) = (x = y).
Proof. exact (@lem7932982 A x y). Qed.
Lemma lem7932986 {A : Type'} (x : type6 A) (y : type6 A) : (term5 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem7932979 A y) (@lem7932983 A x y)). Qed.
Lemma lem7932988 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7932989 {A : Type'} (x : type6 A) (y : type6 A) : (term6 A x y) = (x = y).
Proof. exact (@lem7932988 (x = y)). Qed.
Lemma lem7932992 {A : Type'} (x : type6 A) (y : type6 A) : (term5 A x y) = (x = y).
Proof. exact (TRANS (@lem7932986 A x y) (@lem7932989 A x y)). Qed.
Lemma lem7932993 {A : Type'} (x : type6 A) (y : type6 A) : (term7 A x y) = (term6 A x y).
Proof. exact (MK_COMB (@lem7932971 A x) (@lem7932992 A x y)). Qed.
Lemma lem7932995 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7932996 {A : Type'} (x : type6 A) (y : type6 A) : (term6 A x y) = (x = y).
Proof. exact (@lem7932995 (x = y)). Qed.
Lemma lem7932999 {A : Type'} (x : type6 A) (y : type6 A) : (term7 A x y) = (x = y).
Proof. exact (TRANS (@lem7932993 A x y) (@lem7932996 A x y)). Qed.
Lemma lem7933000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7933001 {A : Type'} (x : type6 A) (y : type6 A) : (term8 A x y) = (term9 A x y).
Proof. exact (MK_COMB (@lem7933000) (@lem7932999 A x y)). Qed.
Lemma lem7933004 {A : Type'} (x : type6 A) (y : type6 A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem7933005 {A : Type'} (x : type6 A) (y : type6 A) : (term10 A x y) = (term11 A x y).
Proof. exact (MK_COMB (@lem7933001 A x y) (@lem7933004 A x y)). Qed.
Lemma lem7933009 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7933010 {A : Type'} (x : type6 A) (y : type6 A) : (term11 A x y) = True.
Proof. exact (@lem7933009 (x = y)). Qed.
Lemma lem7933011 {A : Type'} (x : type6 A) (y : type6 A) : (term10 A x y) = True.
Proof. exact (TRANS (@lem7933005 A x y) (@lem7933010 A x y)). Qed.
Lemma lem7933012 {A : Type'} (x : type6 A) : (term12 A x) = (term13 A).
Proof. exact (fun_ext (fun y : type6 A => @lem7933011 A x y)). Qed.
Lemma lem7933013 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7933014 {A : Type'} (x : type6 A) : (term14 A x) = (term15 A).
Proof. exact (MK_COMB (@lem7933013 A) (@lem7933012 A x)). Qed.
Lemma lem7933016 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7933017 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem7933016 (type6 A) t). Qed.
Lemma lem7933018 {A : Type'} : (term15 A) = True.
Proof. exact (@lem7933017 A True). Qed.
Lemma lem7933019 {A : Type'} (x : type6 A) : (term14 A x) = True.
Proof. exact (TRANS (@lem7933014 A x) (@lem7933018 A)). Qed.
Lemma lem7933020 {A : Type'} : (term18 A) = (term13 A).
Proof. exact (fun_ext (fun x : type6 A => @lem7933019 A x)). Qed.
Lemma lem7933021 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7933022 {A : Type'} : (term19 A) = (term15 A).
Proof. exact (MK_COMB (@lem7933021 A) (@lem7933020 A)). Qed.
Lemma lem7933024 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7933025 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (@lem7933024 (type6 A) t). Qed.
Lemma lem7933026 {A : Type'} : (term15 A) = True.
Proof. exact (@lem7933025 A True). Qed.
Lemma lem7933027 {A : Type'} : (term19 A) = True.
Proof. exact (TRANS (@lem7933022 A) (@lem7933026 A)). Qed.
Lemma lem7933028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7933029 {A : Type'} : (term20 A) = (and True).
Proof. exact (MK_COMB (@lem7933028) (@lem7933027 A)). Qed.
Lemma lem7933030 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem7933031 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (MK_COMB (@lem7933029 A) (@lem7933030 A)). Qed.
Lemma lem7933033 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7933034 {A : Type'} : (term23 A) = (term21 A).
Proof. exact (@lem7933033 (term21 A)). Qed.
Lemma lem7933035 {A : Type'} : (term22 A) = (term21 A).
Proof. exact (TRANS (@lem7933031 A) (@lem7933034 A)). Qed.
Lemma lem7933036 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (SYM (@lem7933035 A)). Qed.
Lemma lem7933038 {M N : Type'} : term24 M N.
Proof. exact (EQ_MP (@lem7637206 M N) (@lem7640378 M N)). Qed.
Lemma lem7933039 {A : Type'} : term25 A.
Proof. exact (@lem7933038 (finite_sum A A) unit). Qed.
Lemma lem7933047 {M N : Type'} : (@dimindex (finite_sum M N) (@UNIV (finite_sum M N))) = (term26 M N).
Proof. exact (EQ_MP (@lem7640410 M N) (@lem7640437 M N)). Qed.
Lemma lem7933048 {A : Type'} : (@dimindex (finite_sum A A) (@UNIV (finite_sum A A))) = (term27 A).
Proof. exact (@lem7933047 A A). Qed.
Lemma lem7933050 (n : nat) : (Nat.add n n) = (term28 n).
Proof. exact (EQ_MP (@lem7932276 n) (@lem7932275 n)). Qed.
Lemma lem7933051 {A : Type'} : (term27 A) = (term29 A).
Proof. exact (@lem7933050 (@dimindex A (@UNIV A))). Qed.
Lemma lem7933052 {A : Type'} : (@dimindex (finite_sum A A) (@UNIV (finite_sum A A))) = (term29 A).
Proof. exact (TRANS (@lem7933048 A) (@lem7933051 A)). Qed.
Lemma lem7933057 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem7933058 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem7933057) (@lem7933052 A)). Qed.
Lemma lem7933060 : (@dimindex unit (@UNIV unit)) = term32.
Proof. exact (@lem7603427 (@lem7603370)). Qed.
Lemma lem7933061 {A : Type'} : (term33 A) = (term3 A).
Proof. exact (MK_COMB (@lem7933058 A) (@lem7933060)). Qed.
Lemma lem7933064 {A : Type'} : (@HAS_SIZE (finite_sum (finite_sum A A) unit) (@UNIV (finite_sum (finite_sum A A) unit))) = (@HAS_SIZE (finite_sum (finite_sum A A) unit) (@UNIV (finite_sum (finite_sum A A) unit))).
Proof. exact (eq_refl (@HAS_SIZE (finite_sum (finite_sum A A) unit) (@UNIV (finite_sum (finite_sum A A) unit)))). Qed.
Lemma lem7933065 {A : Type'} : (term25 A) = (term21 A).
Proof. exact (MK_COMB (@lem7933064 A) (@lem7933061 A)). Qed.
Lemma lem7933066 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7933067 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem7933066) (@lem7933065 A)). Qed.
Lemma lem7933074 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (eq_refl (term21 A)). Qed.
Lemma lem7933075 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem7933067 A) (@lem7933074 A)). Qed.
Lemma lem7933077 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7933078 {A : Type'} : (term37 A) = True.
Proof. exact (@lem7933077 (term21 A)). Qed.
Lemma lem7933079 {A : Type'} : (term36 A) = True.
Proof. exact (TRANS (@lem7933075 A) (@lem7933078 A)). Qed.
Lemma lem7933080 {A : Type'} : True = (term36 A).
Proof. exact (SYM (@lem7933079 A)). Qed.
Lemma lem7933081 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem7933080 A) (@lem0)). Qed.
Lemma lem7933082 {A : Type'} : term21 A.
Proof. exact (@lem7933081 A (@lem7933039 A)). Qed.
Lemma lem7933083 {A : Type'} : term22 A.
Proof. exact (EQ_MP (@lem7933036 A) (@lem7933082 A)). Qed.
Lemma lem7933084 {A : Type'} : term38 A.
Proof. exact (@lem7932952 A (@lem7933083 A)). Qed.
Lemma lem7933085 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : term39 A.
Proof. exact (EQ_MP (@lem7932405 A h1) (@lem7933084 A)). Qed.
Lemma lem7933086 {A : Type'} : ((@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) = (term39 A).
Proof. exact (prop_ext (fun h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) => @lem7933085 A h1) (fun h1 : term39 A => @lem7932948 A)). Qed.
