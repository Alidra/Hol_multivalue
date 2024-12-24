Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_IMAGE_NONZERO_term_abbrevs.
Require Import ITERATE_IMAGE_NONZERO_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import NEUTRAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7177891 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7177893 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7177894 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7177893 A B C h1 op). Qed.
Lemma lem7177895 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7177896 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7177895 A B C op) (@lem7177894 A B C op h1)). Qed.
Lemma lem7177897 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7177898 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7177896 A B C op h1 (@lem7177897 C op h2)). Qed.
Lemma lem7177899 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7177898 A B C op h0 h1). Qed.
Lemma lem7177900 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7177901 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7177899 A B C op h2 (@lem7177900 A B C h1)). Qed.
Lemma lem7177902 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7177901 A B C op h1 h0). Qed.
Lemma lem7177903 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7177902 A B C op h1). Qed.
Lemma lem7177904 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7177903 A B C h0). Qed.
Lemma lem7177905 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7177904 A B C (@lem6155069 A B C)). Qed.
Lemma lem7177906 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7177905 A B C op). Qed.
Lemma lem7177907 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7177909 (h1 : (@neutral real real_add) = term6) : (@neutral real real_add) = term6.
Proof. exact (h1). Qed.
Lemma lem7177910 (h1 : (@neutral real real_add) = term6) : term6 = (@neutral real real_add).
Proof. exact (SYM (@lem7177909 h1)). Qed.
Lemma lem7177911 (h1 : term6 = (@neutral real real_add)) : term6 = (@neutral real real_add).
Proof. exact (h1). Qed.
Lemma lem7177912 (h1 : term6 = (@neutral real real_add)) : (@neutral real real_add) = term6.
Proof. exact (SYM (@lem7177911 h1)). Qed.
Lemma lem7177913 : ((@neutral real real_add) = term6) = (term6 = (@neutral real real_add)).
Proof. exact (prop_ext (fun h1 : (@neutral real real_add) = term6 => @lem7177910 h1) (fun h1 : term6 = (@neutral real real_add) => @lem7177912 h1)). Qed.
Lemma lem7177954 : term6 = (@neutral real real_add).
Proof. exact (EQ_MP (@lem7177913) (@lem7065438)). Qed.
Lemma lem7177955 {A B : Type'} (d : B -> real) (i : A -> B) (x : A) : (term7 A B d i x) = (term7 A B d i x).
Proof. exact (eq_refl (term7 A B d i x)). Qed.
Lemma lem7177956 {A B : Type'} (d : B -> real) (i : A -> B) (x : A) : ((term8 A B d i x) = term6) = ((term8 A B d i x) = (@neutral real real_add)).
Proof. exact (MK_COMB (@lem7177955 A B d i x) (@lem7177954)). Qed.
Lemma lem7177959 {A B : Type'} (s : A -> Prop) (x : A) (i : A -> B) (y : A) : (term9 A B s x i y) = (term9 A B s x i y).
Proof. exact (eq_refl (term9 A B s x i y)). Qed.
Lemma lem7177960 {A B : Type'} (s : A -> Prop) (y : A) (d : B -> real) (i : A -> B) (x : A) : (term10 A B s y d i x) = (term11 A B s y d i x).
Proof. exact (MK_COMB (@lem7177959 A B s x i y) (@lem7177956 A B d i x)). Qed.
Lemma lem7177963 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) (x : A) : (term12 A B s d i x) = (term13 A B s d i x).
Proof. exact (fun_ext (fun y : A => @lem7177960 A B s y d i x)). Qed.
Lemma lem7177964 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7177965 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) (x : A) : (term14 A B s d i x) = (term15 A B s d i x).
Proof. exact (MK_COMB (@lem7177964 A) (@lem7177963 A B s d i x)). Qed.
Lemma lem7177970 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term16 A B s d i) = (term17 A B s d i).
Proof. exact (fun_ext (fun x : A => @lem7177965 A B s d i x)). Qed.
Lemma lem7177971 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7177972 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term18 A B s d i) = (term19 A B s d i).
Proof. exact (MK_COMB (@lem7177971 A) (@lem7177970 A B s d i)). Qed.
Lemma lem7177977 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem7177978 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term21 A B s d i) = (term22 A B s d i).
Proof. exact (MK_COMB (@lem7177977 A s) (@lem7177972 A B s d i)). Qed.
Lemma lem7177981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7177982 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term23 A B s d i) = (term24 A B s d i).
Proof. exact (MK_COMB (@lem7177981) (@lem7177978 A B s d i)). Qed.
Lemma lem7177986 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7177987 {B : Type'} : (@sum B) = (@iterate real B real_add).
Proof. exact (@lem7177986 B). Qed.
Lemma lem7177988 {A B : Type'} (i : A -> B) (s : A -> Prop) : (@IMAGE A B i s) = (@IMAGE A B i s).
Proof. exact (eq_refl (@IMAGE A B i s)). Qed.
Lemma lem7177989 {A B : Type'} (i : A -> B) (s : A -> Prop) : (term25 A B i s) = (term26 A B i s).
Proof. exact (MK_COMB (@lem7177987 B) (@lem7177988 A B i s)). Qed.
Lemma lem7177990 {B : Type'} (d : B -> real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem7177991 {A B : Type'} (i : A -> B) (s : A -> Prop) (d : B -> real) : (term27 A B i s d) = (term28 A B i s d).
Proof. exact (MK_COMB (@lem7177989 A B i s) (@lem7177990 B d)). Qed.
Lemma lem7177992 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7177993 {A B : Type'} (i : A -> B) (s : A -> Prop) (d : B -> real) : (term29 A B i s d) = (term30 A B i s d).
Proof. exact (MK_COMB (@lem7177992) (@lem7177991 A B i s d)). Qed.
Lemma lem7177995 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7177996 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7177995 A). Qed.
Lemma lem7177997 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7177998 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7177996 A) (@lem7177997 A s)). Qed.
Lemma lem7177999 {A B : Type'} (d : B -> real) (i : A -> B) : (@o A B real d i) = (@o A B real d i).
Proof. exact (eq_refl (@o A B real d i)). Qed.
Lemma lem7178000 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term31 A B s d i) = (term32 A B s d i).
Proof. exact (MK_COMB (@lem7177998 A s) (@lem7177999 A B d i)). Qed.
Lemma lem7178001 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : ((term27 A B i s d) = (term31 A B s d i)) = ((term28 A B i s d) = (term32 A B s d i)).
Proof. exact (MK_COMB (@lem7177993 A B i s d) (@lem7178000 A B s d i)). Qed.
Lemma lem7178004 {A B : Type'} (s : A -> Prop) (d : B -> real) (i : A -> B) : (term33 A B s d i) = (term34 A B s d i).
Proof. exact (MK_COMB (@lem7177982 A B s d i) (@lem7178001 A B s d i)). Qed.
Lemma lem7178007 {A B : Type'} (d : B -> real) (i : A -> B) : (term35 A B d i) = (term36 A B d i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7178004 A B s d i)). Qed.
Lemma lem7178008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178009 {A B : Type'} (d : B -> real) (i : A -> B) : (term37 A B d i) = (term38 A B d i).
Proof. exact (MK_COMB (@lem7178008 A) (@lem7178007 A B d i)). Qed.
Lemma lem7178014 {A B : Type'} (d : B -> real) : (term39 A B d) = (term40 A B d).
Proof. exact (fun_ext (fun i : A -> B => @lem7178009 A B d i)). Qed.
Lemma lem7178015 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7178016 {A B : Type'} (d : B -> real) : (term41 A B d) = (term42 A B d).
Proof. exact (MK_COMB (@lem7178015 A B) (@lem7178014 A B d)). Qed.
Lemma lem7178021 {A B : Type'} : (term43 A B) = (term44 A B).
Proof. exact (fun_ext (fun d : B -> real => @lem7178016 A B d)). Qed.
Lemma lem7178022 {B : Type'} : (@all (B -> real)) = (@all (B -> real)).
Proof. exact (eq_refl (@all (B -> real))). Qed.
Lemma lem7178023 {A B : Type'} : (term45 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem7178022 B) (@lem7178021 A B)). Qed.
Lemma lem7178028 {A B : Type'} : (term46 A B) = (term45 A B).
Proof. exact (SYM (@lem7178023 A B)). Qed.
Lemma lem7178030 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7177907 A B C op) (@lem7177906 A B C op)). Qed.
Lemma lem7178031 {A B : Type'} (op : type1627) : term47 A B op.
Proof. exact (@lem7178030 A B real op). Qed.
Lemma lem7178032 {A B : Type'} : term48 A B.
Proof. exact (@lem7178031 A B real_add). Qed.
Lemma lem7178034 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7177891) (@lem7067132)). Qed.
Lemma lem7178035 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178034)). Qed.
Lemma lem7178036 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178035) (@lem0)). Qed.
Lemma lem7178037 {A B : Type'} : term46 A B.
Proof. exact (@lem7178032 A B (@lem7178036)). Qed.
Lemma lem7178038 {A B : Type'} : term45 A B.
Proof. exact (EQ_MP (@lem7178028 A B) (@lem7178037 A B)). Qed.
