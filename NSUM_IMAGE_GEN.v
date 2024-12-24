Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_IMAGE_GEN_term_abbrevs.
Require Import ITERATE_IMAGE_GEN_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6993064 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6993066 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem6993067 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem6993066 A B C h1 op). Qed.
Lemma lem6993068 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem6993069 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem6993068 A B C op) (@lem6993067 A B C op h1)). Qed.
Lemma lem6993070 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6993071 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem6993069 A B C op h1 (@lem6993070 C op h2)). Qed.
Lemma lem6993072 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem6993071 A B C op h0 h1). Qed.
Lemma lem6993073 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem6993074 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem6993072 A B C op h2 (@lem6993073 A B C h1)). Qed.
Lemma lem6993075 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6993074 A B C op h1 h0). Qed.
Lemma lem6993076 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem6993075 A B C op h1). Qed.
Lemma lem6993077 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem6993076 A B C h0). Qed.
Lemma lem6993078 {A B C : Type'} : term0 A B C.
Proof. exact (@lem6993077 A B C (@lem6158399 A B C)). Qed.
Lemma lem6993079 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem6993078 A B C op). Qed.
Lemma lem6993080 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem6993099 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6993100 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6993099 A). Qed.
Lemma lem6993101 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6993102 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6993100 A) (@lem6993101 A s)). Qed.
Lemma lem6993103 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6993104 {A : Type'} (s : A -> Prop) (g : A -> nat) : (@nsum A s g) = (@iterate nat A Nat.add s g).
Proof. exact (MK_COMB (@lem6993102 A s) (@lem6993103 A g)). Qed.
Lemma lem6993105 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6993106 {A : Type'} (s : A -> Prop) (g : A -> nat) : (term6 A s g) = (term7 A s g).
Proof. exact (MK_COMB (@lem6993105) (@lem6993104 A s g)). Qed.
Lemma lem6993108 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6993109 {B : Type'} : (@nsum B) = (@iterate nat B Nat.add).
Proof. exact (@lem6993108 B). Qed.
Lemma lem6993110 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@IMAGE A B f s).
Proof. exact (eq_refl (@IMAGE A B f s)). Qed.
Lemma lem6993111 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term8 A B f s) = (term9 A B f s).
Proof. exact (MK_COMB (@lem6993109 B) (@lem6993110 A B f s)). Qed.
Lemma lem6993113 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6993114 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6993113 A). Qed.
Lemma lem6993123 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term10 A B s f y) = (term10 A B s f y).
Proof. exact (eq_refl (term10 A B s f y)). Qed.
Lemma lem6993124 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) : (term11 A B s f y) = (term12 A B s f y).
Proof. exact (MK_COMB (@lem6993114 A) (@lem6993123 A B s f y)). Qed.
Lemma lem6993125 {A : Type'} (g : A -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem6993126 {A B : Type'} (s : A -> Prop) (f : A -> B) (y : B) (g : A -> nat) : (term13 A B s f y g) = (term14 A B s f y g).
Proof. exact (MK_COMB (@lem6993124 A B s f y) (@lem6993125 A g)). Qed.
Lemma lem6993127 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term15 A B s f g) = (term16 A B s f g).
Proof. exact (fun_ext (fun y : B => @lem6993126 A B s f y g)). Qed.
Lemma lem6993128 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term17 A B s f g) = (term18 A B s f g).
Proof. exact (MK_COMB (@lem6993111 A B f s) (@lem6993127 A B s f g)). Qed.
Lemma lem6993129 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : ((@nsum A s g) = (term17 A B s f g)) = ((@iterate nat A Nat.add s g) = (term18 A B s f g)).
Proof. exact (MK_COMB (@lem6993106 A s g) (@lem6993128 A B s f g)). Qed.
Lemma lem6993132 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem6993133 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : A -> nat) : (term20 A B s f g) = (term21 A B s f g).
Proof. exact (MK_COMB (@lem6993132 A s) (@lem6993129 A B s f g)). Qed.
Lemma lem6993136 {A B : Type'} (f : A -> B) (g : A -> nat) : (term22 A B f g) = (term23 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6993133 A B s f g)). Qed.
Lemma lem6993137 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6993138 {A B : Type'} (f : A -> B) (g : A -> nat) : (term24 A B f g) = (term25 A B f g).
Proof. exact (MK_COMB (@lem6993137 A) (@lem6993136 A B f g)). Qed.
Lemma lem6993143 {A B : Type'} (f : A -> B) : (term26 A B f) = (term27 A B f).
Proof. exact (fun_ext (fun g : A -> nat => @lem6993138 A B f g)). Qed.
Lemma lem6993144 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6993145 {A B : Type'} (f : A -> B) : (term28 A B f) = (term29 A B f).
Proof. exact (MK_COMB (@lem6993144 A) (@lem6993143 A B f)). Qed.
Lemma lem6993150 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem6993145 A B f)). Qed.
Lemma lem6993151 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem6993152 {A B : Type'} : (term32 A B) = (term33 A B).
Proof. exact (MK_COMB (@lem6993151 A B) (@lem6993150 A B)). Qed.
Lemma lem6993157 {A B : Type'} : (term33 A B) = (term32 A B).
Proof. exact (SYM (@lem6993152 A B)). Qed.
Lemma lem6993159 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem6993080 A B C op) (@lem6993079 A B C op)). Qed.
Lemma lem6993160 {A B : Type'} (op : type1606) : term34 A B op.
Proof. exact (@lem6993159 A B nat op). Qed.
Lemma lem6993161 {A B : Type'} : term35 A B.
Proof. exact (@lem6993160 A B Nat.add). Qed.
Lemma lem6993163 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6993064) (@lem6924403)). Qed.
Lemma lem6993164 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6993163)). Qed.
Lemma lem6993165 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6993164) (@lem0)). Qed.
Lemma lem6993166 {A B : Type'} : term33 A B.
Proof. exact (@lem6993161 A B (@lem6993165)). Qed.
Lemma lem6993167 {A B : Type'} : term32 A B.
Proof. exact (EQ_MP (@lem6993157 A B) (@lem6993166 A B)). Qed.
