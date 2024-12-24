Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7921507_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm7919632_spec.
Lemma lem7919721 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7919722 {A B : Type'} : (term1 A B) = (term2 A B).
Proof. exact (@lem7919721 (term1 A B)). Qed.
Lemma lem7919723 {A B : Type'} : (term2 A B) = (term1 A B).
Proof. exact (SYM (@lem7919722 A B)). Qed.
Lemma lem7919724 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7919725 {A B : Type'} : term4 A B.
Proof. exact (@lem7919632 A B). Qed.
Lemma lem7919728 {B : Type'} : term5 B.
Proof. exact (@lem7919632 B B). Qed.
Lemma lem7919731 {A : Type'} : term5 A.
Proof. exact (@lem7919632 A A). Qed.
Lemma lem7919737 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7919738 {A B : Type'} : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7919737 A B h0). Qed.
Lemma lem7919739 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7919740 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem7919741 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7919739 A B h2 (@lem7919740 A B h1)). Qed.
Lemma lem7919742 {A B : Type'} (h1 : term6 A B) : term8 A B.
Proof. exact (fun h0 : term7 A B => @lem7919741 A B h1 h0). Qed.
Lemma lem7919743 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem7919744 {A B : Type'} (h1 : term6 A B) (h2 : term7 A B) : term6 A B.
Proof. exact (@lem7919742 A B h1 (@lem7919743 A B h2)). Qed.
Lemma lem7919745 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (fun h0 : term6 A B => @lem7919744 A B h0 h1). Qed.
Lemma lem7919746 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term7 A B => @lem7919745 A B h0). Qed.
Lemma lem7919749 {A B : Type'} : term7 A B.
Proof. exact (@lem7919746 A B (@lem7919738 A B)). Qed.
Lemma lem7919750 {A B : Type'} : term7 A B.
Proof. exact (@lem7919749 A B). Qed.
Lemma lem7919832 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7919833 {B : Type'} : (term10 B) = (term11 B).
Proof. exact (@lem7919832 (term5 B)). Qed.
Lemma lem7919844 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (eq_refl (term12 A B)). Qed.
Lemma lem7919845 {A B : Type'} : (term13 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7919844 A B) (@lem7919833 B)). Qed.
Lemma lem7919848 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (eq_refl (term15 A)). Qed.
Lemma lem7919849 {A B : Type'} : (term16 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem7919848 A) (@lem7919845 A B)). Qed.
Lemma lem7919852 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (eq_refl (term18 A B)). Qed.
Lemma lem7919859 {A B : Type'} : (term6 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7919852 A B) (@lem7919849 A B)). Qed.
Lemma lem7919864 {B : Type'} (r : nat) : ((term20 B r) = ((term21 B r) = r)) = ((term20 B r) = ((term21 B r) = r)).
Proof. exact (eq_refl ((term20 B r) = ((term21 B r) = r))). Qed.
Lemma lem7919865 {B : Type'} : (term22 B) = (term22 B).
Proof. exact (fun_ext (fun r : nat => @lem7919864 B r)). Qed.
Lemma lem7919866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919867 {B : Type'} : (term23 B) = (term23 B).
Proof. exact (MK_COMB (@lem7919866) (@lem7919865 B)). Qed.
Lemma lem7919868 {B : Type'} (a : finite_prod B B) : ((term24 B a) = a) = ((term24 B a) = a).
Proof. exact (eq_refl ((term24 B a) = a)). Qed.
Lemma lem7919869 {B : Type'} : (term25 B) = (term25 B).
Proof. exact (fun_ext (fun a : finite_prod B B => @lem7919868 B a)). Qed.
Lemma lem7919870 {B : Type'} : (@all (finite_prod B B)) = (@all (finite_prod B B)).
Proof. exact (eq_refl (@all (finite_prod B B))). Qed.
Lemma lem7919871 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (MK_COMB (@lem7919870 B) (@lem7919869 B)). Qed.
Lemma lem7919872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7919873 {B : Type'} : (term27 B) = (term27 B).
Proof. exact (MK_COMB (@lem7919872) (@lem7919871 B)). Qed.
Lemma lem7919874 {B : Type'} : (term5 B) = (term5 B).
Proof. exact (MK_COMB (@lem7919873 B) (@lem7919867 B)). Qed.
Lemma lem7919875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7919876 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem7919875) (@lem7919874 B)). Qed.
Lemma lem7919881 {A B : Type'} (r : nat) : ((term28 A B r) = ((term29 A B r) = r)) = ((term28 A B r) = ((term29 A B r) = r)).
Proof. exact (eq_refl ((term28 A B r) = ((term29 A B r) = r))). Qed.
Lemma lem7919882 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (fun_ext (fun r : nat => @lem7919881 A B r)). Qed.
Lemma lem7919883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919884 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem7919883) (@lem7919882 A B)). Qed.
Lemma lem7919885 {A B : Type'} (a : finite_prod A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7919886 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_prod A B => @lem7919885 A B a)). Qed.
Lemma lem7919887 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7919888 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7919887 A B) (@lem7919886 A B)). Qed.
Lemma lem7919889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7919890 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7919889) (@lem7919888 A B)). Qed.
Lemma lem7919891 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem7919890 A B) (@lem7919884 A B)). Qed.
Lemma lem7919892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7919893 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem7919892) (@lem7919891 A B)). Qed.
Lemma lem7919894 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem7919893 A B) (@lem7919876 B)). Qed.
Lemma lem7919899 {A : Type'} (r : nat) : ((term20 A r) = ((term21 A r) = r)) = ((term20 A r) = ((term21 A r) = r)).
Proof. exact (eq_refl ((term20 A r) = ((term21 A r) = r))). Qed.
Lemma lem7919900 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun r : nat => @lem7919899 A r)). Qed.
Lemma lem7919901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7919902 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem7919901) (@lem7919900 A)). Qed.
Lemma lem7919903 {A : Type'} (a : finite_prod A A) : ((term24 A a) = a) = ((term24 A a) = a).
Proof. exact (eq_refl ((term24 A a) = a)). Qed.
Lemma lem7919904 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (fun_ext (fun a : finite_prod A A => @lem7919903 A a)). Qed.
Lemma lem7919905 {A : Type'} : (@all (finite_prod A A)) = (@all (finite_prod A A)).
Proof. exact (eq_refl (@all (finite_prod A A))). Qed.
Lemma lem7919906 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7919905 A) (@lem7919904 A)). Qed.
Lemma lem7919907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7919908 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem7919907) (@lem7919906 A)). Qed.
Lemma lem7919909 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem7919908 A) (@lem7919902 A)). Qed.
Lemma lem7919910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7919911 {A : Type'} : (term15 A) = (term15 A).
Proof. exact (MK_COMB (@lem7919910) (@lem7919909 A)). Qed.
Lemma lem7919912 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem7919911 A) (@lem7919894 A B)). Qed.
Lemma lem7919917 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term36 A B x x') = (term36 A B x x').
Proof. exact (eq_refl (term36 A B x x')). Qed.
Lemma lem7919918 {A B : Type'} (x : finite_prod A B) : (term37 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7919917 A B x x')). Qed.
Lemma lem7919919 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7919920 {A B : Type'} (x : finite_prod A B) : (term38 A B x) = (term38 A B x).
Proof. exact (MK_COMB (@lem7919919) (@lem7919918 A B x)). Qed.
Lemma lem7919921 {A B : Type'} : (term39 A B) = (term39 A B).
Proof. exact (fun_ext (fun x : finite_prod A B => @lem7919920 A B x)). Qed.
Lemma lem7919922 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7919923 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem7919922 A B) (@lem7919921 A B)). Qed.
Lemma lem7919924 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7919925 {A B : Type'} : (term3 A B) = (term3 A B).
Proof. exact (MK_COMB (@lem7919924) (@lem7919923 A B)). Qed.
Lemma lem7919926 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7919927 {A B : Type'} : (term18 A B) = (term18 A B).
Proof. exact (MK_COMB (@lem7919926) (@lem7919925 A B)). Qed.
Lemma lem7919928 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem7919927 A B) (@lem7919912 A B)). Qed.
Lemma lem7919993 {A B : Type'} : (term6 A B) = (term19 A B).
Proof. exact (TRANS (@lem7919859 A B) (@lem7919928 A B)). Qed.
Lemma lem7919994 {A B : Type'} : (term19 A B) = (term6 A B).
Proof. exact (SYM (@lem7919993 A B)). Qed.
Lemma lem7919995 {A B : Type'} (h1 : term3 A B) : term3 A B.
Proof. exact (h1). Qed.
Lemma lem7919997 {A B : Type'} (h1 : term4 A B) : term4 A B.
Proof. exact (h1). Qed.
Lemma lem7920005 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term40 A B x x') = (term41 A B x x').
Proof. exact (@lem17045 (x = (@mk_finite_prod A B x')) (term28 A B x')). Qed.
Lemma lem7920006 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem7920007 {A B : Type'} (x : finite_prod A B) : (term44 A B x) = (term45 A B x).
Proof. exact (@lem7920006 (term37 A B x)). Qed.
Lemma lem7920008 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term46 A B x x') = (term36 A B x x').
Proof. exact (eq_refl (term46 A B x x')). Qed.
Lemma lem7920009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7920010 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term47 A B x x') = (term40 A B x x').
Proof. exact (MK_COMB (@lem7920009) (@lem7920008 A B x x')). Qed.
Lemma lem7920011 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term47 A B x x') = (term41 A B x x').
Proof. exact (TRANS (@lem7920010 A B x x') (@lem7920005 A B x x')). Qed.
Lemma lem7920012 {A B : Type'} (x : finite_prod A B) : (term48 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7920011 A B x x')). Qed.
Lemma lem7920013 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920014 {A B : Type'} (x : finite_prod A B) : (term45 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7920013) (@lem7920012 A B x)). Qed.
Lemma lem7920015 {A B : Type'} (x : finite_prod A B) : (term44 A B x) = (term50 A B x).
Proof. exact (TRANS (@lem7920007 A B x) (@lem7920014 A B x)). Qed.
Lemma lem7920016 {A B : Type'} (P : type36 A B) : (term51 A B P) = (term52 A B P).
Proof. exact (@lem18392 (finite_prod A B) P). Qed.
Lemma lem7920017 {A B : Type'} : (term3 A B) = (term53 A B).
Proof. exact (@lem7920016 A B (term39 A B)). Qed.
Lemma lem7920018 {A B : Type'} (x : finite_prod A B) : (term54 A B x) = (term38 A B x).
Proof. exact (eq_refl (term54 A B x)). Qed.
Lemma lem7920019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7920020 {A B : Type'} (x : finite_prod A B) : (term55 A B x) = (term44 A B x).
Proof. exact (MK_COMB (@lem7920019) (@lem7920018 A B x)). Qed.
Lemma lem7920021 {A B : Type'} (x : finite_prod A B) : (term55 A B x) = (term50 A B x).
Proof. exact (TRANS (@lem7920020 A B x) (@lem7920015 A B x)). Qed.
Lemma lem7920022 {A B : Type'} : (term56 A B) = (term57 A B).
Proof. exact (fun_ext (fun x : finite_prod A B => @lem7920021 A B x)). Qed.
Lemma lem7920023 {A B : Type'} : (@ex (finite_prod A B)) = (@ex (finite_prod A B)).
Proof. exact (eq_refl (@ex (finite_prod A B))). Qed.
Lemma lem7920024 {A B : Type'} : (term53 A B) = (term58 A B).
Proof. exact (MK_COMB (@lem7920023 A B) (@lem7920022 A B)). Qed.
Lemma lem7920081 {A B : Type'} : (term3 A B) = (term58 A B).
Proof. exact (TRANS (@lem7920017 A B) (@lem7920024 A B)). Qed.
Lemma lem7920082 {A B : Type'} (h1 : term3 A B) : term58 A B.
Proof. exact (EQ_MP (@lem7920081 A B) (@lem7919995 A B h1)). Qed.
Lemma lem7920241 {A B : Type'} (a : finite_prod A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7920242 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_prod A B => @lem7920241 A B a)). Qed.
Lemma lem7920243 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7920244 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7920243 A B) (@lem7920242 A B)). Qed.
Lemma lem7920259 {A B : Type'} (r : nat) : ((term28 A B r) = ((term29 A B r) = r)) = (term59 A B r).
Proof. exact (@lem17784 (term28 A B r) ((term29 A B r) = r)). Qed.
Lemma lem7920260 {A B : Type'} : (term30 A B) = (term60 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920259 A B r)). Qed.
Lemma lem7920261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920262 {A B : Type'} : (term31 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7920261) (@lem7920260 A B)). Qed.
Lemma lem7920263 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7920264 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7920263) (@lem7920244 A B)). Qed.
Lemma lem7920265 {A B : Type'} : (term4 A B) = (term62 A B).
Proof. exact (MK_COMB (@lem7920264 A B) (@lem7920262 A B)). Qed.
Lemma lem7920271 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term63 A P Q) = (term64 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7920272 (P : nat -> Prop) (Q : nat -> Prop) : (term65 P Q) = (term66 P Q).
Proof. exact (@lem7920271 nat P Q). Qed.
Lemma lem7920273 {A B : Type'} : (term67 A B) = (term68 A B).
Proof. exact (@lem7920272 (term69 A B) (term70 A B)). Qed.
Lemma lem7920274 {A B : Type'} (r : nat) : (term71 A B r) = (term72 A B r).
Proof. exact (eq_refl (term71 A B r)). Qed.
Lemma lem7920275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7920276 {A B : Type'} (r : nat) : (term73 A B r) = (term74 A B r).
Proof. exact (MK_COMB (@lem7920275) (@lem7920274 A B r)). Qed.
Lemma lem7920277 {A B : Type'} (r : nat) : (term75 A B r) = (term76 A B r).
Proof. exact (eq_refl (term75 A B r)). Qed.
Lemma lem7920278 {A B : Type'} (r : nat) : (term77 A B r) = (term59 A B r).
Proof. exact (MK_COMB (@lem7920276 A B r) (@lem7920277 A B r)). Qed.
Lemma lem7920279 {A B : Type'} : (term78 A B) = (term60 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920278 A B r)). Qed.
Lemma lem7920280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920281 {A B : Type'} : (term67 A B) = (term61 A B).
Proof. exact (MK_COMB (@lem7920280) (@lem7920279 A B)). Qed.
Lemma lem7920282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7920283 {A B : Type'} : (term79 A B) = (term80 A B).
Proof. exact (MK_COMB (@lem7920282) (@lem7920281 A B)). Qed.
Lemma lem7920284 {A B : Type'} (r : nat) : (term71 A B r) = (term72 A B r).
Proof. exact (eq_refl (term71 A B r)). Qed.
Lemma lem7920285 {A B : Type'} : (term81 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920284 A B r)). Qed.
Lemma lem7920286 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920287 {A B : Type'} : (term82 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7920286) (@lem7920285 A B)). Qed.
Lemma lem7920288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7920289 {A B : Type'} : (term84 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem7920288) (@lem7920287 A B)). Qed.
Lemma lem7920290 {A B : Type'} (r : nat) : (term75 A B r) = (term76 A B r).
Proof. exact (eq_refl (term75 A B r)). Qed.
Lemma lem7920291 {A B : Type'} : (term86 A B) = (term70 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920290 A B r)). Qed.
Lemma lem7920292 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920293 {A B : Type'} : (term87 A B) = (term88 A B).
Proof. exact (MK_COMB (@lem7920292) (@lem7920291 A B)). Qed.
Lemma lem7920294 {A B : Type'} : (term68 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem7920289 A B) (@lem7920293 A B)). Qed.
Lemma lem7920295 {A B : Type'} : ((term67 A B) = (term68 A B)) = ((term61 A B) = (term89 A B)).
Proof. exact (MK_COMB (@lem7920283 A B) (@lem7920294 A B)). Qed.
Lemma lem7920296 {A B : Type'} : (term61 A B) = (term89 A B).
Proof. exact (EQ_MP (@lem7920295 A B) (@lem7920273 A B)). Qed.
Lemma lem7920393 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (eq_refl (term35 A B)). Qed.
Lemma lem7920396 {A B : Type'} : (term62 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem7920393 A B) (@lem7920296 A B)). Qed.
Lemma lem7920397 {A B : Type'} : (term4 A B) = (term90 A B).
Proof. exact (TRANS (@lem7920265 A B) (@lem7920396 A B)). Qed.
Lemma lem7920398 {A B : Type'} (h1 : term4 A B) : term90 A B.
Proof. exact (EQ_MP (@lem7920397 A B) (@lem7919997 A B h1)). Qed.
Lemma lem7920557 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (h1). Qed.
Lemma lem7920687 {A B : Type'} (r : nat) : (term76 A B r) = (term76 A B r).
Proof. exact (eq_refl (term76 A B r)). Qed.
Lemma lem7920688 {A B : Type'} : (term70 A B) = (term70 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920687 A B r)). Qed.
Lemma lem7920689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920690 {A B : Type'} : (term88 A B) = (term88 A B).
Proof. exact (MK_COMB (@lem7920689) (@lem7920688 A B)). Qed.
Lemma lem7920725 {A B : Type'} (r : nat) : (term72 A B r) = (term72 A B r).
Proof. exact (eq_refl (term72 A B r)). Qed.
Lemma lem7920726 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920725 A B r)). Qed.
Lemma lem7920727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920728 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7920727) (@lem7920726 A B)). Qed.
Lemma lem7920729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7920730 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem7920729) (@lem7920728 A B)). Qed.
Lemma lem7920731 {A B : Type'} : (term89 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem7920730 A B) (@lem7920690 A B)). Qed.
Lemma lem7920740 {A B : Type'} (a : finite_prod A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7920741 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_prod A B => @lem7920740 A B a)). Qed.
Lemma lem7920742 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7920743 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7920742 A B) (@lem7920741 A B)). Qed.
Lemma lem7920744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7920745 {A B : Type'} : (term35 A B) = (term35 A B).
Proof. exact (MK_COMB (@lem7920744) (@lem7920743 A B)). Qed.
Lemma lem7920746 {A B : Type'} : (term90 A B) = (term90 A B).
Proof. exact (MK_COMB (@lem7920745 A B) (@lem7920731 A B)). Qed.
Lemma lem7920747 {A B : Type'} (h1 : term4 A B) : term90 A B.
Proof. exact (EQ_MP (@lem7920746 A B) (@lem7920398 A B h1)). Qed.
Lemma lem7920877 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term41 A B x x') = (term41 A B x x').
Proof. exact (eq_refl (term41 A B x x')). Qed.
Lemma lem7920878 {A B : Type'} (x : finite_prod A B) : (term49 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7920877 A B x x')). Qed.
Lemma lem7920879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920880 {A B : Type'} (x : finite_prod A B) : (term50 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7920879) (@lem7920878 A B x)). Qed.
Lemma lem7920881 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (EQ_MP (@lem7920880 A B x) (@lem7920557 A B x h1)). Qed.
Lemma lem7920886 {A B : Type'} (h1 : term4 A B) : term89 A B.
Proof. exact (proj2 (@lem7920747 A B h1)). Qed.
Lemma lem7920887 {A B : Type'} (h1 : term4 A B) : term34 A B.
Proof. exact (proj1 (@lem7920747 A B h1)). Qed.
Lemma lem7920889 {A B : Type'} (h1 : term4 A B) : term83 A B.
Proof. exact (proj1 (@lem7920886 A B h1)). Qed.
Lemma lem7920901 {A B : Type'} (x : finite_prod A B) (x' : nat) : (term41 A B x x') = (term41 A B x x').
Proof. exact (eq_refl (term41 A B x x')). Qed.
Lemma lem7920902 {A B : Type'} (x : finite_prod A B) : (term49 A B x) = (term49 A B x).
Proof. exact (fun_ext (fun x' : nat => @lem7920901 A B x x')). Qed.
Lemma lem7920903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920905 {A B : Type'} (x : finite_prod A B) : (term50 A B x) = (term50 A B x).
Proof. exact (MK_COMB (@lem7920903) (@lem7920902 A B x)). Qed.
Lemma lem7920906 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) : term50 A B x.
Proof. exact (EQ_MP (@lem7920905 A B x) (@lem7920881 A B x h1)). Qed.
Lemma lem7920941 {A B : Type'} (a : finite_prod A B) : ((term32 A B a) = a) = ((term32 A B a) = a).
Proof. exact (eq_refl ((term32 A B a) = a)). Qed.
Lemma lem7920942 {A B : Type'} : (term33 A B) = (term33 A B).
Proof. exact (fun_ext (fun a : finite_prod A B => @lem7920941 A B a)). Qed.
Lemma lem7920943 {A B : Type'} : (@all (finite_prod A B)) = (@all (finite_prod A B)).
Proof. exact (eq_refl (@all (finite_prod A B))). Qed.
Lemma lem7920945 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem7920943 A B) (@lem7920942 A B)). Qed.
Lemma lem7920946 {A B : Type'} (h1 : term4 A B) : term34 A B.
Proof. exact (EQ_MP (@lem7920945 A B) (@lem7920887 A B h1)). Qed.
Lemma lem7920954 {A B : Type'} (r : nat) : (term72 A B r) = (term72 A B r).
Proof. exact (eq_refl (term72 A B r)). Qed.
Lemma lem7920955 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun r : nat => @lem7920954 A B r)). Qed.
Lemma lem7920956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7920958 {A B : Type'} : (term83 A B) = (term83 A B).
Proof. exact (MK_COMB (@lem7920956) (@lem7920955 A B)). Qed.
Lemma lem7920959 {A B : Type'} (h1 : term4 A B) : term83 A B.
Proof. exact (EQ_MP (@lem7920958 A B) (@lem7920889 A B h1)). Qed.
Lemma lem7921006 {A B : Type'} (_103675 : nat) (x : finite_prod A B) (h1 : term50 A B x) : term91 A B x _103675.
Proof. exact (@lem7920906 A B x h1 _103675). Qed.
Lemma lem7921007 {A B : Type'} (x : finite_prod A B) (_103675 : nat) : (term91 A B x _103675) = (term41 A B x _103675).
Proof. exact (eq_refl (term91 A B x _103675)). Qed.
Lemma lem7921018 {A B : Type'} (_103679 : finite_prod A B) (h1 : term4 A B) : term92 A B _103679.
Proof. exact (@lem7920946 A B h1 _103679). Qed.
Lemma lem7921019 {A B : Type'} (_103679 : finite_prod A B) : (term92 A B _103679) = ((term32 A B _103679) = _103679).
Proof. exact (eq_refl (term92 A B _103679)). Qed.
Lemma lem7921021 {A B : Type'} (_103680 : nat) (h1 : term4 A B) : term71 A B _103680.
Proof. exact (@lem7920959 A B h1 _103680). Qed.
Lemma lem7921022 {A B : Type'} (_103680 : nat) : (term71 A B _103680) = (term72 A B _103680).
Proof. exact (eq_refl (term71 A B _103680)). Qed.
Lemma lem7921041 {A B : Type'} (_103675 : nat) (x : finite_prod A B) (h1 : term50 A B x) : term41 A B x _103675.
Proof. exact (EQ_MP (@lem7921007 A B x _103675) (@lem7921006 A B _103675 x h1)). Qed.
Lemma lem7921063 {A B : Type'} (_103680 : nat) (h1 : term4 A B) : term72 A B _103680.
Proof. exact (EQ_MP (@lem7921022 A B _103680) (@lem7921021 A B _103680 h1)). Qed.
Lemma lem7921119 {A B : Type'} : (@dest_finite_prod A B) = (@dest_finite_prod A B).
Proof. exact (eq_refl (@dest_finite_prod A B)). Qed.
Lemma lem7921120 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) (h1 : _103693 = _103694) : _103693 = _103694.
Proof. exact (h1). Qed.
Lemma lem7921121 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) (h1 : _103693 = _103694) : (@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694).
Proof. exact (MK_COMB (@lem7921119 A B) (@lem7921120 A B _103693 _103694 h1)). Qed.
Lemma lem7921122 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : term93 A B _103693 _103694.
Proof. exact (fun h0 : _103693 = _103694 => @lem7921121 A B _103693 _103694 h0). Qed.
Lemma lem7921124 (a : Prop) (b : Prop) : (a -> b) = (term94 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7921125 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term93 A B _103693 _103694) = (term95 A B _103693 _103694).
Proof. exact (@lem7921124 (_103693 = _103694) ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694))). Qed.
Lemma lem7921126 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : term95 A B _103693 _103694.
Proof. exact (EQ_MP (@lem7921125 A B _103693 _103694) (@lem7921122 A B _103693 _103694)). Qed.
Lemma lem7921222 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : term96 A B x y z.
Proof. exact (@lem21385 (finite_prod A B) x y z). Qed.
Lemma lem7921228 {A B : Type'} (_103679 : finite_prod A B) (h1 : term4 A B) : (term32 A B _103679) = _103679.
Proof. exact (EQ_MP (@lem7921019 A B _103679) (@lem7921018 A B _103679 h1)). Qed.
Lemma lem7921229 {A B : Type'} (_103679 : finite_prod A B) (h1 : term4 A B) : (term32 A B _103679) = _103679.
Proof. exact (@lem7921228 A B _103679 h1). Qed.
Lemma lem7921230 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (@lem7921229 A B x h1). Qed.
Lemma lem7921231 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term97 A B x.
Proof. exact (fun h0 : term98 A B x => @lem7921230 A B x h1). Qed.
Lemma lem7921233 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921234 {A B : Type'} (x : finite_prod A B) : (term97 A B x) = ((term32 A B x) = x).
Proof. exact (@lem7921233 ((term32 A B x) = x)). Qed.
Lemma lem7921235 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (EQ_MP (@lem7921234 A B x) (@lem7921231 A B x h1)). Qed.
Lemma lem7921237 {A B : Type'} (x : finite_prod A B) : x = x.
Proof. exact (@lem21386 (finite_prod A B) x). Qed.
Lemma lem7921238 {A B : Type'} (x : finite_prod A B) : x = x.
Proof. exact (@lem7921237 A B x). Qed.
Lemma lem7921239 {A B : Type'} (x : finite_prod A B) : (term32 A B x) = (term32 A B x).
Proof. exact (@lem7921238 A B (term32 A B x)). Qed.
Lemma lem7921240 {A B : Type'} (x : finite_prod A B) : term100 A B x.
Proof. exact (fun h0 : term101 A B x => @lem7921239 A B x). Qed.
Lemma lem7921242 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921243 {A B : Type'} (x : finite_prod A B) : (term100 A B x) = ((term32 A B x) = (term32 A B x)).
Proof. exact (@lem7921242 ((term32 A B x) = (term32 A B x))). Qed.
Lemma lem7921244 {A B : Type'} (x : finite_prod A B) : (term32 A B x) = (term32 A B x).
Proof. exact (EQ_MP (@lem7921243 A B x) (@lem7921240 A B x)). Qed.
Lemma lem7921262 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7921263 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term102 A B x y z) = (term103 A B y x z).
Proof. exact (@lem7921262 (y = z) (term104 A B x z)). Qed.
Lemma lem7921273 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) : (term105 A B x y) = (term105 A B x y).
Proof. exact (eq_refl (term105 A B x y)). Qed.
Lemma lem7921274 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term96 A B x y z) = (term106 A B y x z).
Proof. exact (MK_COMB (@lem7921273 A B x y) (@lem7921263 A B y x z)). Qed.
Lemma lem7921278 (q : Prop) (p : Prop) (r : Prop) : (term107 p q r) = (term107 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7921279 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term106 A B y x z) = (term108 A B y x z).
Proof. exact (@lem7921278 (y = z) (term104 A B x y) (term104 A B x z)). Qed.
Lemma lem7921301 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term96 A B x y z) = (term108 A B y x z).
Proof. exact (TRANS (@lem7921274 A B y x z) (@lem7921279 A B y x z)). Qed.
Lemma lem7921302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7921303 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term109 A B x y z) = (term110 A B y x z).
Proof. exact (MK_COMB (@lem7921302) (@lem7921301 A B y x z)). Qed.
Lemma lem7921325 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term108 A B y x z) = (term108 A B y x z).
Proof. exact (eq_refl (term108 A B y x z)). Qed.
Lemma lem7921326 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : ((term96 A B x y z) = (term108 A B y x z)) = ((term108 A B y x z) = (term108 A B y x z)).
Proof. exact (MK_COMB (@lem7921303 A B y x z) (@lem7921325 A B y x z)). Qed.
Lemma lem7921328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7921329 (x : Prop) : (x = x) = True.
Proof. exact (@lem7921328 Prop x). Qed.
Lemma lem7921330 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : ((term108 A B y x z) = (term108 A B y x z)) = True.
Proof. exact (@lem7921329 (term108 A B y x z)). Qed.
Lemma lem7921331 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : ((term96 A B x y z) = (term108 A B y x z)) = True.
Proof. exact (TRANS (@lem7921326 A B y x z) (@lem7921330 A B y x z)). Qed.
Lemma lem7921332 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : True = ((term96 A B x y z) = (term108 A B y x z)).
Proof. exact (SYM (@lem7921331 A B y x z)). Qed.
Lemma lem7921333 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term96 A B x y z) = (term108 A B y x z).
Proof. exact (EQ_MP (@lem7921332 A B y x z) (@lem0)). Qed.
Lemma lem7921334 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : term108 A B y x z.
Proof. exact (EQ_MP (@lem7921333 A B y x z) (@lem7921222 A B x y z)). Qed.
Lemma lem7921336 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7921337 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : (term108 A B y x z) = (term112 A B x y z).
Proof. exact (@lem7921336 (term113 A B y x z) (y = z)). Qed.
Lemma lem7921339 (a : Prop) (b : Prop) : (term114 a b) = (term115 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7921340 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term116 A B y x z) = (term117 A B y x z).
Proof. exact (@lem7921339 (term104 A B x y) (term104 A B x z)). Qed.
Lemma lem7921342 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7921343 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) : (term119 A B x y) = (x = y).
Proof. exact (@lem7921342 (x = y)). Qed.
Lemma lem7921344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7921345 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) : (term120 A B x y) = (term121 A B x y).
Proof. exact (MK_COMB (@lem7921344) (@lem7921343 A B x y)). Qed.
Lemma lem7921347 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7921348 {A B : Type'} (x : finite_prod A B) (z : finite_prod A B) : (term119 A B x z) = (x = z).
Proof. exact (@lem7921347 (x = z)). Qed.
Lemma lem7921349 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term117 A B y x z) = (term122 A B y x z).
Proof. exact (MK_COMB (@lem7921345 A B x y) (@lem7921348 A B x z)). Qed.
Lemma lem7921350 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term116 A B y x z) = (term122 A B y x z).
Proof. exact (TRANS (@lem7921340 A B y x z) (@lem7921349 A B y x z)). Qed.
Lemma lem7921351 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921352 {A B : Type'} (y : finite_prod A B) (x : finite_prod A B) (z : finite_prod A B) : (term123 A B y x z) = (term124 A B y x z).
Proof. exact (MK_COMB (@lem7921351) (@lem7921350 A B y x z)). Qed.
Lemma lem7921353 {A B : Type'} (y : finite_prod A B) (z : finite_prod A B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7921354 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : (term112 A B x y z) = (term125 A B x y z).
Proof. exact (MK_COMB (@lem7921352 A B y x z) (@lem7921353 A B y z)). Qed.
Lemma lem7921355 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : (term108 A B y x z) = (term125 A B x y z).
Proof. exact (TRANS (@lem7921337 A B x y z) (@lem7921354 A B x y z)). Qed.
Lemma lem7921357 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term126 A B x.
Proof. exact (conj (@lem7921235 A B x h1) (@lem7921244 A B x)). Qed.
Lemma lem7921359 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : term125 A B x y z.
Proof. exact (EQ_MP (@lem7921355 A B x y z) (@lem7921334 A B y x z)). Qed.
Lemma lem7921360 {A B : Type'} (x : finite_prod A B) (y : finite_prod A B) (z : finite_prod A B) : term125 A B x y z.
Proof. exact (@lem7921359 A B x y z). Qed.
Lemma lem7921361 {A B : Type'} (x : finite_prod A B) : term127 A B x.
Proof. exact (@lem7921360 A B (term32 A B x) x (term32 A B x)). Qed.
Lemma lem7921364 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (@lem7921361 A B x (@lem7921357 A B x h1)). Qed.
Lemma lem7921365 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (@lem7921364 A B x h1). Qed.
Lemma lem7921366 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term128 A B x.
Proof. exact (fun h0 : term129 A B x => @lem7921365 A B x h1). Qed.
Lemma lem7921368 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921369 {A B : Type'} (x : finite_prod A B) : (term128 A B x) = (x = (term32 A B x)).
Proof. exact (@lem7921368 (x = (term32 A B x))). Qed.
Lemma lem7921370 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : x = (term32 A B x).
Proof. exact (EQ_MP (@lem7921369 A B x) (@lem7921366 A B x h1)). Qed.
Lemma lem7921372 {A B : Type'} (_103679 : finite_prod A B) (h1 : term4 A B) : (term32 A B _103679) = _103679.
Proof. exact (EQ_MP (@lem7921019 A B _103679) (@lem7921018 A B _103679 h1)). Qed.
Lemma lem7921373 {A B : Type'} (_103679 : finite_prod A B) (h1 : term4 A B) : (term32 A B _103679) = _103679.
Proof. exact (@lem7921372 A B _103679 h1). Qed.
Lemma lem7921374 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (@lem7921373 A B x h1). Qed.
Lemma lem7921375 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term97 A B x.
Proof. exact (fun h0 : term98 A B x => @lem7921374 A B x h1). Qed.
Lemma lem7921377 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921378 {A B : Type'} (x : finite_prod A B) : (term97 A B x) = ((term32 A B x) = x).
Proof. exact (@lem7921377 ((term32 A B x) = x)). Qed.
Lemma lem7921379 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term32 A B x) = x.
Proof. exact (EQ_MP (@lem7921378 A B x) (@lem7921375 A B x h1)). Qed.
Lemma lem7921385 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7921386 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term95 A B _103693 _103694) = (term130 A B _103693 _103694).
Proof. exact (@lem7921385 ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694)) (term104 A B _103693 _103694)). Qed.
Lemma lem7921396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7921397 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term131 A B _103693 _103694) = (term132 A B _103693 _103694).
Proof. exact (MK_COMB (@lem7921396) (@lem7921386 A B _103693 _103694)). Qed.
Lemma lem7921407 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term130 A B _103693 _103694) = (term130 A B _103693 _103694).
Proof. exact (eq_refl (term130 A B _103693 _103694)). Qed.
Lemma lem7921408 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : ((term95 A B _103693 _103694) = (term130 A B _103693 _103694)) = ((term130 A B _103693 _103694) = (term130 A B _103693 _103694)).
Proof. exact (MK_COMB (@lem7921397 A B _103693 _103694) (@lem7921407 A B _103693 _103694)). Qed.
Lemma lem7921410 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7921411 (x : Prop) : (x = x) = True.
Proof. exact (@lem7921410 Prop x). Qed.
Lemma lem7921412 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : ((term130 A B _103693 _103694) = (term130 A B _103693 _103694)) = True.
Proof. exact (@lem7921411 (term130 A B _103693 _103694)). Qed.
Lemma lem7921413 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : ((term95 A B _103693 _103694) = (term130 A B _103693 _103694)) = True.
Proof. exact (TRANS (@lem7921408 A B _103693 _103694) (@lem7921412 A B _103693 _103694)). Qed.
Lemma lem7921414 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : True = ((term95 A B _103693 _103694) = (term130 A B _103693 _103694)).
Proof. exact (SYM (@lem7921413 A B _103693 _103694)). Qed.
Lemma lem7921415 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term95 A B _103693 _103694) = (term130 A B _103693 _103694).
Proof. exact (EQ_MP (@lem7921414 A B _103693 _103694) (@lem0)). Qed.
Lemma lem7921416 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : term130 A B _103693 _103694.
Proof. exact (EQ_MP (@lem7921415 A B _103693 _103694) (@lem7921126 A B _103693 _103694)). Qed.
Lemma lem7921418 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7921419 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term130 A B _103693 _103694) = (term133 A B _103693 _103694).
Proof. exact (@lem7921418 (term104 A B _103693 _103694) ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694))). Qed.
Lemma lem7921421 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7921422 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term119 A B _103693 _103694) = (_103693 = _103694).
Proof. exact (@lem7921421 (_103693 = _103694)). Qed.
Lemma lem7921423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921424 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term134 A B _103693 _103694) = (term135 A B _103693 _103694).
Proof. exact (MK_COMB (@lem7921423) (@lem7921422 A B _103693 _103694)). Qed.
Lemma lem7921425 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694)) = ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694)).
Proof. exact (eq_refl ((@dest_finite_prod A B _103693) = (@dest_finite_prod A B _103694))). Qed.
Lemma lem7921426 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term133 A B _103693 _103694) = (term93 A B _103693 _103694).
Proof. exact (MK_COMB (@lem7921424 A B _103693 _103694) (@lem7921425 A B _103693 _103694)). Qed.
Lemma lem7921427 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : (term130 A B _103693 _103694) = (term93 A B _103693 _103694).
Proof. exact (TRANS (@lem7921419 A B _103693 _103694) (@lem7921426 A B _103693 _103694)). Qed.
Lemma lem7921430 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : term93 A B _103693 _103694.
Proof. exact (EQ_MP (@lem7921427 A B _103693 _103694) (@lem7921416 A B _103693 _103694)). Qed.
Lemma lem7921431 {A B : Type'} (_103693 : finite_prod A B) (_103694 : finite_prod A B) : term93 A B _103693 _103694.
Proof. exact (@lem7921430 A B _103693 _103694). Qed.
Lemma lem7921432 {A B : Type'} (x : finite_prod A B) : term136 A B x.
Proof. exact (@lem7921431 A B (term32 A B x) x). Qed.
Lemma lem7921435 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_prod A B x).
Proof. exact (@lem7921432 A B x (@lem7921379 A B x h1)). Qed.
Lemma lem7921436 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_prod A B x).
Proof. exact (@lem7921435 A B x h1). Qed.
Lemma lem7921437 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term138 A B x.
Proof. exact (fun h0 : term139 A B x => @lem7921436 A B x h1). Qed.
Lemma lem7921439 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921440 {A B : Type'} (x : finite_prod A B) : (term138 A B x) = ((term137 A B x) = (@dest_finite_prod A B x)).
Proof. exact (@lem7921439 ((term137 A B x) = (@dest_finite_prod A B x))). Qed.
Lemma lem7921441 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : (term137 A B x) = (@dest_finite_prod A B x).
Proof. exact (EQ_MP (@lem7921440 A B x) (@lem7921437 A B x h1)). Qed.
Lemma lem7921443 (b : Prop) (a : Prop) : (a \/ b) = (term111 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7921444 {A B : Type'} (_103680 : nat) : (term72 A B _103680) = (term140 A B _103680).
Proof. exact (@lem7921443 (term141 A B _103680) (term28 A B _103680)). Qed.
Lemma lem7921446 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7921447 {A B : Type'} (_103680 : nat) : (term142 A B _103680) = ((term29 A B _103680) = _103680).
Proof. exact (@lem7921446 ((term29 A B _103680) = _103680)). Qed.
Lemma lem7921448 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7921449 {A B : Type'} (_103680 : nat) : (term143 A B _103680) = (term144 A B _103680).
Proof. exact (MK_COMB (@lem7921448) (@lem7921447 A B _103680)). Qed.
Lemma lem7921450 {A B : Type'} (_103680 : nat) : (term28 A B _103680) = (term28 A B _103680).
Proof. exact (eq_refl (term28 A B _103680)). Qed.
Lemma lem7921451 {A B : Type'} (_103680 : nat) : (term140 A B _103680) = (term145 A B _103680).
Proof. exact (MK_COMB (@lem7921449 A B _103680) (@lem7921450 A B _103680)). Qed.
Lemma lem7921452 {A B : Type'} (_103680 : nat) : (term72 A B _103680) = (term145 A B _103680).
Proof. exact (TRANS (@lem7921444 A B _103680) (@lem7921451 A B _103680)). Qed.
Lemma lem7921455 {A B : Type'} (_103680 : nat) (h1 : term4 A B) : term145 A B _103680.
Proof. exact (EQ_MP (@lem7921452 A B _103680) (@lem7921063 A B _103680 h1)). Qed.
Lemma lem7921456 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term146 A B x.
Proof. exact (@lem7921455 A B (@dest_finite_prod A B x) h1). Qed.
Lemma lem7921459 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (@lem7921456 A B x h1 (@lem7921441 A B x h1)). Qed.
Lemma lem7921460 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (@lem7921459 A B x h1). Qed.
Lemma lem7921461 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term148 A B x.
Proof. exact (fun h0 : term149 A B x => @lem7921460 A B x h1). Qed.
Lemma lem7921463 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921464 {A B : Type'} (x : finite_prod A B) : (term148 A B x) = (term147 A B x).
Proof. exact (@lem7921463 (term147 A B x)). Qed.
Lemma lem7921465 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term147 A B x.
Proof. exact (EQ_MP (@lem7921464 A B x) (@lem7921461 A B x h1)). Qed.
Lemma lem7921467 (a : Prop) (b : Prop) : (term150 a b) = (term151 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem7921468 {A B : Type'} (x : finite_prod A B) (_103675 : nat) : (term41 A B x _103675) = (term40 A B x _103675).
Proof. exact (@lem7921467 (x = (@mk_finite_prod A B _103675)) (term28 A B _103675)). Qed.
Lemma lem7921470 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7921471 {A B : Type'} (x : finite_prod A B) (_103675 : nat) : (term40 A B x _103675) = (term152 A B x _103675).
Proof. exact (@lem7921470 (term36 A B x _103675)). Qed.
Lemma lem7921472 {A B : Type'} (x : finite_prod A B) (_103675 : nat) : (term41 A B x _103675) = (term152 A B x _103675).
Proof. exact (TRANS (@lem7921468 A B x _103675) (@lem7921471 A B x _103675)). Qed.
Lemma lem7921474 {A B : Type'} (x : finite_prod A B) (h1 : term4 A B) : term153 A B x.
Proof. exact (conj (@lem7921370 A B x h1) (@lem7921465 A B x h1)). Qed.
Lemma lem7921476 {A B : Type'} (_103675 : nat) (x : finite_prod A B) (h1 : term50 A B x) : term152 A B x _103675.
Proof. exact (EQ_MP (@lem7921472 A B x _103675) (@lem7921041 A B _103675 x h1)). Qed.
Lemma lem7921477 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) : term154 A B x.
Proof. exact (@lem7921476 A B (@dest_finite_prod A B x) x h1). Qed.
Lemma lem7921480 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (@lem7921477 A B x h1 (@lem7921474 A B x h2)). Qed.
Lemma lem7921481 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : term155.
Proof. exact (fun h0 : ~ False => @lem7921480 A B x h1 h2). Qed.
Lemma lem7921483 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7921484 : term155 = False.
Proof. exact (@lem7921483 False). Qed.
Lemma lem7921485 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7921484) (@lem7921481 A B x h1 h2)). Qed.
Lemma lem7921486 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : (term50 A B x) = False.
Proof. exact (prop_ext (fun h3 : term50 A B x => @lem7921485 A B x h1 h2) (fun h3 : False => @lem7920906 A B x h1)). Qed.
Lemma lem7921487 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7921486 A B x h1 h2) (@lem7920906 A B x h1)). Qed.
Lemma lem7921488 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : (term50 A B x) = False.
Proof. exact (prop_ext (fun h3 : term50 A B x => @lem7921487 A B x h1 h2) (fun h3 : False => @lem7920881 A B x h1)). Qed.
Lemma lem7921489 {A B : Type'} (x : finite_prod A B) (h1 : term50 A B x) (h2 : term4 A B) : False.
Proof. exact (EQ_MP (@lem7921488 A B x h1 h2) (@lem7920881 A B x h1)). Qed.
Lemma lem7921490 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : False.
Proof. exact (ex_elim (@lem7920082 A B h1) (fun x : finite_prod A B => fun h0 : term57 A B x => @lem7921489 A B x h0 h2)). Qed.
Lemma lem7921491 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : term10 B.
Proof. exact (fun h0 : term5 B => @lem7921490 A B h1 h2). Qed.
Lemma lem7921492 {B : Type'} : (term10 B) = (term11 B).
Proof. exact (@lem69 (term5 B)). Qed.
Lemma lem7921493 {A B : Type'} (h1 : term3 A B) (h2 : term4 A B) : term11 B.
Proof. exact (EQ_MP (@lem7921492 B) (@lem7921491 A B h1 h2)). Qed.
Lemma lem7921494 {A B : Type'} (h1 : term3 A B) : term14 A B.
Proof. exact (fun h0 : term4 A B => @lem7921493 A B h1 h0). Qed.
Lemma lem7921495 {A B : Type'} (h1 : term3 A B) : term17 A B.
Proof. exact (fun h0 : term5 A => @lem7921494 A B h1). Qed.
Lemma lem7921496 {A B : Type'} : term19 A B.
Proof. exact (fun h0 : term3 A B => @lem7921495 A B h0). Qed.
Lemma lem7921497 {A B : Type'} : term6 A B.
Proof. exact (EQ_MP (@lem7919994 A B) (@lem7921496 A B)). Qed.
Lemma lem7921499 {A B : Type'} : term6 A B.
Proof. exact (@lem7919750 A B (@lem7921497 A B)). Qed.
Lemma lem7921500 {A B : Type'} (h1 : term3 A B) : term16 A B.
Proof. exact (@lem7921499 A B (@lem7919724 A B h1)). Qed.
Lemma lem7921501 {A B : Type'} (h1 : term3 A B) : term13 A B.
Proof. exact (@lem7921500 A B h1 (@lem7919731 A)). Qed.
Lemma lem7921502 {A B : Type'} (h1 : term3 A B) : term10 B.
Proof. exact (@lem7921501 A B h1 (@lem7919725 A B)). Qed.
Lemma lem7921503 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (@lem7921502 A B h1 (@lem7919728 B)). Qed.
Lemma lem7921504 {A B : Type'} (h1 : term3 A B) : (term3 A B) = False.
Proof. exact (prop_ext (fun h2 : term3 A B => @lem7921503 A B h1) (fun h2 : False => @lem7919724 A B h1)). Qed.
Lemma lem7921505 {A B : Type'} (h1 : term3 A B) : False.
Proof. exact (EQ_MP (@lem7921504 A B h1) (@lem7919724 A B h1)). Qed.
Lemma lem7921506 {A B : Type'} : term2 A B.
Proof. exact (fun h0 : term3 A B => @lem7921505 A B h0). Qed.
Lemma lem7921507 {A B : Type'} : term1 A B.
Proof. exact (EQ_MP (@lem7919723 A B) (@lem7921506 A B)). Qed.
