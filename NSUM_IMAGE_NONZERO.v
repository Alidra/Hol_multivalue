Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_IMAGE_NONZERO_term_abbrevs.
Require Import ITERATE_IMAGE_NONZERO_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7017696 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7017698 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7017699 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7017698 A B C h1 op). Qed.
Lemma lem7017700 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7017701 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7017700 A B C op) (@lem7017699 A B C op h1)). Qed.
Lemma lem7017702 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7017703 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7017701 A B C op h1 (@lem7017702 C op h2)). Qed.
Lemma lem7017704 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7017703 A B C op h0 h1). Qed.
Lemma lem7017705 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7017706 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7017704 A B C op h2 (@lem7017705 A B C h1)). Qed.
Lemma lem7017707 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7017706 A B C op h1 h0). Qed.
Lemma lem7017708 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7017707 A B C op h1). Qed.
Lemma lem7017709 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7017708 A B C h0). Qed.
Lemma lem7017710 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7017709 A B C (@lem6155069 A B C)). Qed.
Lemma lem7017711 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7017710 A B C op). Qed.
Lemma lem7017712 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7017714 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem7017715 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem7017714 h1)). Qed.
Lemma lem7017716 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem7017717 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem7017716 h1)). Qed.
Lemma lem7017718 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem7017715 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem7017717 h1)). Qed.
Lemma lem7017759 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem7017718) (@lem6921993)). Qed.
Lemma lem7017760 {A B : Type'} (d : B -> nat) (i : A -> B) (x : A) : (term6 A B d i x) = (term6 A B d i x).
Proof. exact (eq_refl (term6 A B d i x)). Qed.
Lemma lem7017761 {A B : Type'} (d : B -> nat) (i : A -> B) (x : A) : ((term7 A B d i x) = (NUMERAL 0)) = ((term7 A B d i x) = (@neutral nat Nat.add)).
Proof. exact (MK_COMB (@lem7017760 A B d i x) (@lem7017759)). Qed.
Lemma lem7017764 {A B : Type'} (s : A -> Prop) (x : A) (i : A -> B) (y : A) : (term8 A B s x i y) = (term8 A B s x i y).
Proof. exact (eq_refl (term8 A B s x i y)). Qed.
Lemma lem7017765 {A B : Type'} (s : A -> Prop) (y : A) (d : B -> nat) (i : A -> B) (x : A) : (term9 A B s y d i x) = (term10 A B s y d i x).
Proof. exact (MK_COMB (@lem7017764 A B s x i y) (@lem7017761 A B d i x)). Qed.
Lemma lem7017768 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) (x : A) : (term11 A B s d i x) = (term12 A B s d i x).
Proof. exact (fun_ext (fun y : A => @lem7017765 A B s y d i x)). Qed.
Lemma lem7017769 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7017770 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) (x : A) : (term13 A B s d i x) = (term14 A B s d i x).
Proof. exact (MK_COMB (@lem7017769 A) (@lem7017768 A B s d i x)). Qed.
Lemma lem7017775 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term15 A B s d i) = (term16 A B s d i).
Proof. exact (fun_ext (fun x : A => @lem7017770 A B s d i x)). Qed.
Lemma lem7017776 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7017777 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term17 A B s d i) = (term18 A B s d i).
Proof. exact (MK_COMB (@lem7017776 A) (@lem7017775 A B s d i)). Qed.
Lemma lem7017782 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem7017783 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term20 A B s d i) = (term21 A B s d i).
Proof. exact (MK_COMB (@lem7017782 A s) (@lem7017777 A B s d i)). Qed.
Lemma lem7017786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7017787 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term22 A B s d i) = (term23 A B s d i).
Proof. exact (MK_COMB (@lem7017786) (@lem7017783 A B s d i)). Qed.
Lemma lem7017791 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7017792 {B : Type'} : (@nsum B) = (@iterate nat B Nat.add).
Proof. exact (@lem7017791 B). Qed.
Lemma lem7017793 {A B : Type'} (i : A -> B) (s : A -> Prop) : (@IMAGE A B i s) = (@IMAGE A B i s).
Proof. exact (eq_refl (@IMAGE A B i s)). Qed.
Lemma lem7017794 {A B : Type'} (i : A -> B) (s : A -> Prop) : (term24 A B i s) = (term25 A B i s).
Proof. exact (MK_COMB (@lem7017792 B) (@lem7017793 A B i s)). Qed.
Lemma lem7017795 {B : Type'} (d : B -> nat) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem7017796 {A B : Type'} (i : A -> B) (s : A -> Prop) (d : B -> nat) : (term26 A B i s d) = (term27 A B i s d).
Proof. exact (MK_COMB (@lem7017794 A B i s) (@lem7017795 B d)). Qed.
Lemma lem7017797 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7017798 {A B : Type'} (i : A -> B) (s : A -> Prop) (d : B -> nat) : (term28 A B i s d) = (term29 A B i s d).
Proof. exact (MK_COMB (@lem7017797) (@lem7017796 A B i s d)). Qed.
Lemma lem7017800 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7017801 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7017800 A). Qed.
Lemma lem7017802 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7017803 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7017801 A) (@lem7017802 A s)). Qed.
Lemma lem7017804 {A B : Type'} (d : B -> nat) (i : A -> B) : (@o A B nat d i) = (@o A B nat d i).
Proof. exact (eq_refl (@o A B nat d i)). Qed.
Lemma lem7017805 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term30 A B s d i) = (term31 A B s d i).
Proof. exact (MK_COMB (@lem7017803 A s) (@lem7017804 A B d i)). Qed.
Lemma lem7017806 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : ((term26 A B i s d) = (term30 A B s d i)) = ((term27 A B i s d) = (term31 A B s d i)).
Proof. exact (MK_COMB (@lem7017798 A B i s d) (@lem7017805 A B s d i)). Qed.
Lemma lem7017809 {A B : Type'} (s : A -> Prop) (d : B -> nat) (i : A -> B) : (term32 A B s d i) = (term33 A B s d i).
Proof. exact (MK_COMB (@lem7017787 A B s d i) (@lem7017806 A B s d i)). Qed.
Lemma lem7017812 {A B : Type'} (d : B -> nat) (i : A -> B) : (term34 A B d i) = (term35 A B d i).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7017809 A B s d i)). Qed.
Lemma lem7017813 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7017814 {A B : Type'} (d : B -> nat) (i : A -> B) : (term36 A B d i) = (term37 A B d i).
Proof. exact (MK_COMB (@lem7017813 A) (@lem7017812 A B d i)). Qed.
Lemma lem7017819 {A B : Type'} (d : B -> nat) : (term38 A B d) = (term39 A B d).
Proof. exact (fun_ext (fun i : A -> B => @lem7017814 A B d i)). Qed.
Lemma lem7017820 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7017821 {A B : Type'} (d : B -> nat) : (term40 A B d) = (term41 A B d).
Proof. exact (MK_COMB (@lem7017820 A B) (@lem7017819 A B d)). Qed.
Lemma lem7017826 {A B : Type'} : (term42 A B) = (term43 A B).
Proof. exact (fun_ext (fun d : B -> nat => @lem7017821 A B d)). Qed.
Lemma lem7017827 {B : Type'} : (@all (B -> nat)) = (@all (B -> nat)).
Proof. exact (eq_refl (@all (B -> nat))). Qed.
Lemma lem7017828 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem7017827 B) (@lem7017826 A B)). Qed.
Lemma lem7017833 {A B : Type'} : (term45 A B) = (term44 A B).
Proof. exact (SYM (@lem7017828 A B)). Qed.
Lemma lem7017835 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7017712 A B C op) (@lem7017711 A B C op)). Qed.
Lemma lem7017836 {A B : Type'} (op : type1606) : term46 A B op.
Proof. exact (@lem7017835 A B nat op). Qed.
Lemma lem7017837 {A B : Type'} : term47 A B.
Proof. exact (@lem7017836 A B Nat.add). Qed.
Lemma lem7017839 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7017696) (@lem6924403)). Qed.
Lemma lem7017840 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7017839)). Qed.
Lemma lem7017841 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7017840) (@lem0)). Qed.
Lemma lem7017842 {A B : Type'} : term45 A B.
Proof. exact (@lem7017837 A B (@lem7017841)). Qed.
Lemma lem7017843 {A B : Type'} : term44 A B.
Proof. exact (EQ_MP (@lem7017833 A B) (@lem7017842 A B)). Qed.
