Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_UNION_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import SUBSET_DISJOINT_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4466530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (term0 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem4466531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (s = t) = (term0 A t s).
Proof. exact (SYM (@lem4466530 A s t h1)). Qed.
Lemma lem4466532 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (s = t) = (term0 A t s).
Proof. exact (h1). Qed.
Lemma lem4466533 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (term0 A t s) = (s = t).
Proof. exact (SYM (@lem4466532 A t s h1)). Qed.
Lemma lem4466534 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term0 A t s) = (s = t)) = ((s = t) = (term0 A t s)).
Proof. exact (prop_ext (fun h1 : (term0 A t s) = (s = t) => @lem4466531 A s t h1) (fun h1 : (s = t) = (term0 A t s) => @lem4466533 A t s h1)). Qed.
Lemma lem4466535 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4466534 A t s)). Qed.
Lemma lem4466536 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4466537 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (MK_COMB (@lem4466536 A) (@lem4466535 A s)). Qed.
Lemma lem4466538 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4466537 A s)). Qed.
Lemma lem4466539 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4466540 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4466539 A) (@lem4466538 A)). Qed.
Lemma lem4466541 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4466540 A) (@lem3219910 A)). Qed.
Lemma lem4466542 {A K : Type'} (k : K -> Prop) : term9 A K k.
Proof. exact (@lem4466517 A K k). Qed.
Lemma lem4466543 {A K : Type'} (k : K -> Prop) : (term9 A K k) = (term10 A K k).
Proof. exact (eq_refl (term9 A K k)). Qed.
Lemma lem4466544 {A K : Type'} (k : K -> Prop) : term10 A K k.
Proof. exact (EQ_MP (@lem4466543 A K k) (@lem4466542 A K k)). Qed.
Lemma lem4466545 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term11 A K k s.
Proof. exact (@lem4466544 A K k s). Qed.
Lemma lem4466546 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term11 A K k s) = (term12 A K k s).
Proof. exact (eq_refl (term11 A K k s)). Qed.
Lemma lem4466547 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term12 A K k s.
Proof. exact (EQ_MP (@lem4466546 A K k s) (@lem4466545 A K k s)). Qed.
Lemma lem4466548 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term13 A K k s t.
Proof. exact (@lem4466547 A K k s t). Qed.
Lemma lem4466549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term13 A K k s t) = ((term14 A K s k t) = (term15 A K k s t)).
Proof. exact (eq_refl (term13 A K k s t)). Qed.
Lemma lem4466551 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem4466541 A s). Qed.
Lemma lem4466552 {A : Type'} (s : A -> Prop) : (term16 A s) = (term4 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4466553 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem4466552 A s) (@lem4466551 A s)). Qed.
Lemma lem4466554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term17 A s t.
Proof. exact (@lem4466553 A s t). Qed.
Lemma lem4466555 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A s t) = ((s = t) = (term0 A t s)).
Proof. exact (eq_refl (term17 A s t)). Qed.
Lemma lem4466576 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4466555 A t s) (@lem4466554 A s t)). Qed.
Lemma lem4466577 {A K : Type'} (t : type1223 A K) (s : type1223 A K) : (s = t) = (term18 A K t s).
Proof. exact (@lem4466576 (prod K A) t s). Qed.
Lemma lem4466578 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : ((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (term19 A K t k s).
Proof. exact (@lem4466577 A K (@disjoint_union A K k t) (@disjoint_union A K k s)). Qed.
Lemma lem4466582 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term15 A K k s t).
Proof. exact (EQ_MP (@lem4466549 A K k s t) (@lem4466548 A K k s t)). Qed.
Lemma lem4466583 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term15 A K k s t).
Proof. exact (@lem4466582 A K k s t). Qed.
Lemma lem4466590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466591 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term20 A K s k t) = (term21 A K k s t).
Proof. exact (MK_COMB (@lem4466590) (@lem4466583 A K k s t)). Qed.
Lemma lem4466593 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term15 A K k s t).
Proof. exact (EQ_MP (@lem4466549 A K k s t) (@lem4466548 A K k s t)). Qed.
Lemma lem4466594 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term14 A K s k t) = (term15 A K k s t).
Proof. exact (@lem4466593 A K k s t). Qed.
Lemma lem4466595 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term14 A K t k s) = (term15 A K k t s).
Proof. exact (@lem4466594 A K k t s). Qed.
Lemma lem4466602 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term19 A K t k s) = (term22 A K k t s).
Proof. exact (MK_COMB (@lem4466591 A K k s t) (@lem4466595 A K k t s)). Qed.
Lemma lem4466605 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (term22 A K k t s).
Proof. exact (TRANS (@lem4466578 A K t k s) (@lem4466602 A K k t s)). Qed.
Lemma lem4466606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466607 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term23 A K s k t) = (term24 A K k t s).
Proof. exact (MK_COMB (@lem4466606) (@lem4466605 A K k t s)). Qed.
Lemma lem4466617 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4466555 A t s) (@lem4466554 A s t)). Qed.
Lemma lem4466618 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (@lem4466617 A t s). Qed.
Lemma lem4466619 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : ((s i) = (t i)) = (term25 A K t s i).
Proof. exact (@lem4466618 A (t i) (s i)). Qed.
Lemma lem4466622 {K : Type'} (i : K) (k : K -> Prop) : (term26 K i k) = (term26 K i k).
Proof. exact (eq_refl (term26 K i k)). Qed.
Lemma lem4466623 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term27 A K k s t i) = (term28 A K k t s i).
Proof. exact (MK_COMB (@lem4466622 K i k) (@lem4466619 A K t s i)). Qed.
Lemma lem4466626 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term29 A K k s t) = (term30 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4466623 A K k t s i)). Qed.
Lemma lem4466627 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466628 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term31 A K k s t) = (term32 A K k t s).
Proof. exact (MK_COMB (@lem4466627 K) (@lem4466626 A K k t s)). Qed.
Lemma lem4466633 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (((@disjoint_union A K k s) = (@disjoint_union A K k t)) = (term31 A K k s t)) = ((term22 A K k t s) = (term32 A K k t s)).
Proof. exact (MK_COMB (@lem4466607 A K k t s) (@lem4466628 A K k t s)). Qed.
Lemma lem4466638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term33 A K k s) = (term34 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4466633 A K k t s)). Qed.
Lemma lem4466639 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4466640 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term35 A K k s) = (term36 A K k s).
Proof. exact (MK_COMB (@lem4466639 A K) (@lem4466638 A K k s)). Qed.
Lemma lem4466645 {A K : Type'} (k : K -> Prop) : (term37 A K k) = (term38 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4466640 A K k s)). Qed.
Lemma lem4466646 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4466647 {A K : Type'} (k : K -> Prop) : (term39 A K k) = (term40 A K k).
Proof. exact (MK_COMB (@lem4466646 A K) (@lem4466645 A K k)). Qed.
Lemma lem4466652 {A K : Type'} : (term41 A K) = (term42 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4466647 A K k)). Qed.
Lemma lem4466653 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4466654 {A K : Type'} : (term43 A K) = (term44 A K).
Proof. exact (MK_COMB (@lem4466653 K) (@lem4466652 A K)). Qed.
Lemma lem4466659 {A K : Type'} : (term44 A K) = (term43 A K).
Proof. exact (SYM (@lem4466654 A K)). Qed.
Lemma lem4466685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4466686 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (@lem4466685 A s t). Qed.
Lemma lem4466687 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term46 A K s t i) = (term47 A K s t i).
Proof. exact (@lem4466686 A (s i) (t i)). Qed.
Lemma lem4466694 {K : Type'} (i : K) (k : K -> Prop) : (term26 K i k) = (term26 K i k).
Proof. exact (eq_refl (term26 K i k)). Qed.
Lemma lem4466695 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term48 A K k s t i) = (term49 A K k s t i).
Proof. exact (MK_COMB (@lem4466694 K i k) (@lem4466687 A K s t i)). Qed.
Lemma lem4466698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term50 A K k s t) = (term51 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4466695 A K k s t i)). Qed.
Lemma lem4466699 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466700 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term15 A K k s t) = (term52 A K k s t).
Proof. exact (MK_COMB (@lem4466699 K) (@lem4466698 A K k s t)). Qed.
Lemma lem4466705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466706 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term21 A K k s t) = (term53 A K k s t).
Proof. exact (MK_COMB (@lem4466705) (@lem4466700 A K k s t)). Qed.
Lemma lem4466714 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4466715 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (@lem4466714 A s t). Qed.
Lemma lem4466716 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term46 A K t s i) = (term47 A K t s i).
Proof. exact (@lem4466715 A (t i) (s i)). Qed.
Lemma lem4466723 {K : Type'} (i : K) (k : K -> Prop) : (term26 K i k) = (term26 K i k).
Proof. exact (eq_refl (term26 K i k)). Qed.
Lemma lem4466724 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term48 A K k t s i) = (term49 A K k t s i).
Proof. exact (MK_COMB (@lem4466723 K i k) (@lem4466716 A K t s i)). Qed.
Lemma lem4466727 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term50 A K k t s) = (term51 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4466724 A K k t s i)). Qed.
Lemma lem4466728 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466729 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term15 A K k t s) = (term52 A K k t s).
Proof. exact (MK_COMB (@lem4466728 K) (@lem4466727 A K k t s)). Qed.
Lemma lem4466734 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term22 A K k t s) = (term54 A K k t s).
Proof. exact (MK_COMB (@lem4466706 A K k s t) (@lem4466729 A K k t s)). Qed.
Lemma lem4466737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466738 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term24 A K k t s) = (term55 A K k t s).
Proof. exact (MK_COMB (@lem4466737) (@lem4466734 A K k t s)). Qed.
Lemma lem4466748 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4466749 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (@lem4466748 A s t). Qed.
Lemma lem4466750 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term46 A K s t i) = (term47 A K s t i).
Proof. exact (@lem4466749 A (s i) (t i)). Qed.
Lemma lem4466757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466758 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term56 A K s t i) = (term57 A K s t i).
Proof. exact (MK_COMB (@lem4466757) (@lem4466750 A K s t i)). Qed.
Lemma lem4466760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4466761 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term45 A s t).
Proof. exact (@lem4466760 A s t). Qed.
Lemma lem4466762 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term46 A K t s i) = (term47 A K t s i).
Proof. exact (@lem4466761 A (t i) (s i)). Qed.
Lemma lem4466769 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term25 A K t s i) = (term58 A K t s i).
Proof. exact (MK_COMB (@lem4466758 A K s t i) (@lem4466762 A K t s i)). Qed.
Lemma lem4466772 {K : Type'} (i : K) (k : K -> Prop) : (term26 K i k) = (term26 K i k).
Proof. exact (eq_refl (term26 K i k)). Qed.
Lemma lem4466773 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term28 A K k t s i) = (term59 A K k t s i).
Proof. exact (MK_COMB (@lem4466772 K i k) (@lem4466769 A K t s i)). Qed.
Lemma lem4466776 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term30 A K k t s) = (term60 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4466773 A K k t s i)). Qed.
Lemma lem4466777 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466778 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term32 A K k t s) = (term61 A K k t s).
Proof. exact (MK_COMB (@lem4466777 K) (@lem4466776 A K k t s)). Qed.
Lemma lem4466783 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term22 A K k t s) = (term32 A K k t s)) = ((term54 A K k t s) = (term61 A K k t s)).
Proof. exact (MK_COMB (@lem4466738 A K k t s) (@lem4466778 A K k t s)). Qed.
Lemma lem4466788 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term34 A K k s) = (term62 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4466783 A K k t s)). Qed.
Lemma lem4466789 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4466790 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term36 A K k s) = (term63 A K k s).
Proof. exact (MK_COMB (@lem4466789 A K) (@lem4466788 A K k s)). Qed.
Lemma lem4466795 {A K : Type'} (k : K -> Prop) : (term38 A K k) = (term64 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4466790 A K k s)). Qed.
Lemma lem4466796 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4466797 {A K : Type'} (k : K -> Prop) : (term40 A K k) = (term65 A K k).
Proof. exact (MK_COMB (@lem4466796 A K) (@lem4466795 A K k)). Qed.
Lemma lem4466802 {A K : Type'} : (term42 A K) = (term66 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4466797 A K k)). Qed.
Lemma lem4466803 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4466804 {A K : Type'} : (term44 A K) = (term67 A K).
Proof. exact (MK_COMB (@lem4466803 K) (@lem4466802 A K)). Qed.
Lemma lem4466809 {A K : Type'} : (term67 A K) = (term44 A K).
Proof. exact (SYM (@lem4466804 A K)). Qed.
Lemma lem4466833 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466834 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4466833 K P x). Qed.
Lemma lem4466835 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4466834 K k i). Qed.
Lemma lem4466836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466837 {K : Type'} (k : K -> Prop) (i : K) : (term26 K i k) = (term68 K k i).
Proof. exact (MK_COMB (@lem4466836) (@lem4466835 K k i)). Qed.
Lemma lem4466845 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466846 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466845 A P x). Qed.
Lemma lem4466847 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term69 A K x s i) = (s i x).
Proof. exact (@lem4466846 A (s i) x). Qed.
Lemma lem4466848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466849 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term70 A K x s i) = (term71 A K s i x).
Proof. exact (MK_COMB (@lem4466848) (@lem4466847 A K s i x)). Qed.
Lemma lem4466851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466851 A P x). Qed.
Lemma lem4466853 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term69 A K x t i) = (t i x).
Proof. exact (@lem4466852 A (t i) x). Qed.
Lemma lem4466854 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term72 A K s x t i) = (term73 A K s t i x).
Proof. exact (MK_COMB (@lem4466849 A K s i x) (@lem4466853 A K t i x)). Qed.
Lemma lem4466857 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term74 A K s t i) = (term75 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4466854 A K s t i x)). Qed.
Lemma lem4466858 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466859 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term47 A K s t i) = (term76 A K s t i).
Proof. exact (MK_COMB (@lem4466858 A) (@lem4466857 A K s t i)). Qed.
Lemma lem4466864 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term49 A K k s t i) = (term77 A K k s t i).
Proof. exact (MK_COMB (@lem4466837 K k i) (@lem4466859 A K s t i)). Qed.
Lemma lem4466867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term51 A K k s t) = (term78 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4466864 A K k s t i)). Qed.
Lemma lem4466868 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466869 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term52 A K k s t) = (term79 A K k s t).
Proof. exact (MK_COMB (@lem4466868 K) (@lem4466867 A K k s t)). Qed.
Lemma lem4466874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term53 A K k s t) = (term80 A K k s t).
Proof. exact (MK_COMB (@lem4466874) (@lem4466869 A K k s t)). Qed.
Lemma lem4466883 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466884 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4466883 K P x). Qed.
Lemma lem4466885 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4466884 K k i). Qed.
Lemma lem4466886 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466887 {K : Type'} (k : K -> Prop) (i : K) : (term26 K i k) = (term68 K k i).
Proof. exact (MK_COMB (@lem4466886) (@lem4466885 K k i)). Qed.
Lemma lem4466895 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466896 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466895 A P x). Qed.
Lemma lem4466897 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term69 A K x t i) = (t i x).
Proof. exact (@lem4466896 A (t i) x). Qed.
Lemma lem4466898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466899 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term70 A K x t i) = (term71 A K t i x).
Proof. exact (MK_COMB (@lem4466898) (@lem4466897 A K t i x)). Qed.
Lemma lem4466901 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466902 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466901 A P x). Qed.
Lemma lem4466903 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term69 A K x s i) = (s i x).
Proof. exact (@lem4466902 A (s i) x). Qed.
Lemma lem4466904 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term72 A K t x s i) = (term73 A K t s i x).
Proof. exact (MK_COMB (@lem4466899 A K t i x) (@lem4466903 A K s i x)). Qed.
Lemma lem4466907 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term74 A K t s i) = (term75 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4466904 A K t s i x)). Qed.
Lemma lem4466908 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466909 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term47 A K t s i) = (term76 A K t s i).
Proof. exact (MK_COMB (@lem4466908 A) (@lem4466907 A K t s i)). Qed.
Lemma lem4466914 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term49 A K k t s i) = (term77 A K k t s i).
Proof. exact (MK_COMB (@lem4466887 K k i) (@lem4466909 A K t s i)). Qed.
Lemma lem4466917 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term51 A K k t s) = (term78 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4466914 A K k t s i)). Qed.
Lemma lem4466918 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4466919 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term52 A K k t s) = (term79 A K k t s).
Proof. exact (MK_COMB (@lem4466918 K) (@lem4466917 A K k t s)). Qed.
Lemma lem4466924 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term54 A K k t s) = (term81 A K k t s).
Proof. exact (MK_COMB (@lem4466875 A K k s t) (@lem4466919 A K k t s)). Qed.
Lemma lem4466927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4466928 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term55 A K k t s) = (term82 A K k t s).
Proof. exact (MK_COMB (@lem4466927) (@lem4466924 A K k t s)). Qed.
Lemma lem4466936 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466937 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4466936 K P x). Qed.
Lemma lem4466938 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4466937 K k i). Qed.
Lemma lem4466939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466940 {K : Type'} (k : K -> Prop) (i : K) : (term26 K i k) = (term68 K k i).
Proof. exact (MK_COMB (@lem4466939) (@lem4466938 K k i)). Qed.
Lemma lem4466950 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466951 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466950 A P x). Qed.
Lemma lem4466952 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term69 A K x s i) = (s i x).
Proof. exact (@lem4466951 A (s i) x). Qed.
Lemma lem4466953 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466954 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term70 A K x s i) = (term71 A K s i x).
Proof. exact (MK_COMB (@lem4466953) (@lem4466952 A K s i x)). Qed.
Lemma lem4466956 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466957 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466956 A P x). Qed.
Lemma lem4466958 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term69 A K x t i) = (t i x).
Proof. exact (@lem4466957 A (t i) x). Qed.
Lemma lem4466959 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term72 A K s x t i) = (term73 A K s t i x).
Proof. exact (MK_COMB (@lem4466954 A K s i x) (@lem4466958 A K t i x)). Qed.
Lemma lem4466962 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term74 A K s t i) = (term75 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4466959 A K s t i x)). Qed.
Lemma lem4466963 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466964 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term47 A K s t i) = (term76 A K s t i).
Proof. exact (MK_COMB (@lem4466963 A) (@lem4466962 A K s t i)). Qed.
Lemma lem4466969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4466970 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term57 A K s t i) = (term83 A K s t i).
Proof. exact (MK_COMB (@lem4466969) (@lem4466964 A K s t i)). Qed.
Lemma lem4466978 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466979 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466978 A P x). Qed.
Lemma lem4466980 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term69 A K x t i) = (t i x).
Proof. exact (@lem4466979 A (t i) x). Qed.
Lemma lem4466981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4466982 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term70 A K x t i) = (term71 A K t i x).
Proof. exact (MK_COMB (@lem4466981) (@lem4466980 A K t i x)). Qed.
Lemma lem4466984 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4466985 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4466984 A P x). Qed.
Lemma lem4466986 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term69 A K x s i) = (s i x).
Proof. exact (@lem4466985 A (s i) x). Qed.
Lemma lem4466987 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term72 A K t x s i) = (term73 A K t s i x).
Proof. exact (MK_COMB (@lem4466982 A K t i x) (@lem4466986 A K s i x)). Qed.
Lemma lem4466990 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term74 A K t s i) = (term75 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4466987 A K t s i x)). Qed.
Lemma lem4466991 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4466992 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term47 A K t s i) = (term76 A K t s i).
Proof. exact (MK_COMB (@lem4466991 A) (@lem4466990 A K t s i)). Qed.
Lemma lem4466997 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term58 A K t s i) = (term84 A K t s i).
Proof. exact (MK_COMB (@lem4466970 A K s t i) (@lem4466992 A K t s i)). Qed.
Lemma lem4467000 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term59 A K k t s i) = (term85 A K k t s i).
Proof. exact (MK_COMB (@lem4466940 K k i) (@lem4466997 A K t s i)). Qed.
Lemma lem4467003 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term60 A K k t s) = (term86 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467000 A K k t s i)). Qed.
Lemma lem4467004 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467005 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term61 A K k t s) = (term87 A K k t s).
Proof. exact (MK_COMB (@lem4467004 K) (@lem4467003 A K k t s)). Qed.
Lemma lem4467010 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term54 A K k t s) = (term61 A K k t s)) = ((term81 A K k t s) = (term87 A K k t s)).
Proof. exact (MK_COMB (@lem4466928 A K k t s) (@lem4467005 A K k t s)). Qed.
Lemma lem4467013 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term62 A K k s) = (term88 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4467010 A K k t s)). Qed.
Lemma lem4467014 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4467015 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term63 A K k s) = (term89 A K k s).
Proof. exact (MK_COMB (@lem4467014 A K) (@lem4467013 A K k s)). Qed.
Lemma lem4467020 {A K : Type'} (k : K -> Prop) : (term64 A K k) = (term90 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4467015 A K k s)). Qed.
Lemma lem4467021 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4467022 {A K : Type'} (k : K -> Prop) : (term65 A K k) = (term91 A K k).
Proof. exact (MK_COMB (@lem4467021 A K) (@lem4467020 A K k)). Qed.
Lemma lem4467027 {A K : Type'} : (term66 A K) = (term92 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4467022 A K k)). Qed.
Lemma lem4467028 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4467029 {A K : Type'} : (term67 A K) = (term93 A K).
Proof. exact (MK_COMB (@lem4467028 K) (@lem4467027 A K)). Qed.
Lemma lem4467034 {A K : Type'} : (term93 A K) = (term67 A K).
Proof. exact (SYM (@lem4467029 A K)). Qed.
Lemma lem4467036 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4467037 {A K : Type'} : (term93 A K) = (term95 A K).
Proof. exact (@lem4467036 (term93 A K)). Qed.
Lemma lem4467038 {A K : Type'} : (term95 A K) = (term93 A K).
Proof. exact (SYM (@lem4467037 A K)). Qed.
Lemma lem4467039 {A K : Type'} (h1 : term96 A K) : term96 A K.
Proof. exact (h1). Qed.
Lemma lem4467042 {A K : Type'} (h1 : term95 A K) : term95 A K.
Proof. exact (h1). Qed.
Lemma lem4467043 {A K : Type'} : term97 A K.
Proof. exact (fun h0 : term95 A K => @lem4467042 A K h0). Qed.
Lemma lem4467044 {A K : Type'} (h1 : term97 A K) : term97 A K.
Proof. exact (h1). Qed.
Lemma lem4467045 {A K : Type'} (h1 : term95 A K) : term95 A K.
Proof. exact (h1). Qed.
Lemma lem4467046 {A K : Type'} (h1 : term95 A K) (h2 : term97 A K) : term95 A K.
Proof. exact (@lem4467044 A K h2 (@lem4467045 A K h1)). Qed.
Lemma lem4467047 {A K : Type'} (h1 : term95 A K) : term98 A K.
Proof. exact (fun h0 : term97 A K => @lem4467046 A K h1 h0). Qed.
Lemma lem4467048 {A K : Type'} (h1 : term97 A K) : term97 A K.
Proof. exact (h1). Qed.
Lemma lem4467049 {A K : Type'} (h1 : term95 A K) (h2 : term97 A K) : term95 A K.
Proof. exact (@lem4467047 A K h1 (@lem4467048 A K h2)). Qed.
Lemma lem4467050 {A K : Type'} (h1 : term97 A K) : term97 A K.
Proof. exact (fun h0 : term95 A K => @lem4467049 A K h0 h1). Qed.
Lemma lem4467051 {A K : Type'} : term99 A K.
Proof. exact (fun h0 : term97 A K => @lem4467050 A K h0). Qed.
Lemma lem4467054 {A K : Type'} : term97 A K.
Proof. exact (@lem4467051 A K (@lem4467043 A K)). Qed.
Lemma lem4467055 {A K : Type'} : term97 A K.
Proof. exact (@lem4467054 A K). Qed.
Lemma lem4467057 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4467058 {A K : Type'} : (term95 A K) = (term100 A K).
Proof. exact (@lem4467057 (term96 A K)). Qed.
Lemma lem4467060 (t : Prop) : (term101 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4467061 {A K : Type'} : (term100 A K) = (term93 A K).
Proof. exact (@lem4467060 (term93 A K)). Qed.
Lemma lem4467124 {A K : Type'} : (term95 A K) = (term93 A K).
Proof. exact (TRANS (@lem4467058 A K) (@lem4467061 A K)). Qed.
Lemma lem4467129 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term73 A K t s i x) = (term73 A K t s i x).
Proof. exact (eq_refl (term73 A K t s i x)). Qed.
Lemma lem4467130 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term75 A K t s i) = (term75 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467129 A K t s i x)). Qed.
Lemma lem4467131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467132 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term76 A K t s i) = (term76 A K t s i).
Proof. exact (MK_COMB (@lem4467131 A) (@lem4467130 A K t s i)). Qed.
Lemma lem4467137 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term73 A K s t i x) = (term73 A K s t i x).
Proof. exact (eq_refl (term73 A K s t i x)). Qed.
Lemma lem4467138 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term75 A K s t i) = (term75 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467137 A K s t i x)). Qed.
Lemma lem4467139 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467140 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term76 A K s t i) = (term76 A K s t i).
Proof. exact (MK_COMB (@lem4467139 A) (@lem4467138 A K s t i)). Qed.
Lemma lem4467141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467142 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term83 A K s t i) = (term83 A K s t i).
Proof. exact (MK_COMB (@lem4467141) (@lem4467140 A K s t i)). Qed.
Lemma lem4467143 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term84 A K t s i) = (term84 A K t s i).
Proof. exact (MK_COMB (@lem4467142 A K s t i) (@lem4467132 A K t s i)). Qed.
Lemma lem4467146 {K : Type'} (k : K -> Prop) (i : K) : (term68 K k i) = (term68 K k i).
Proof. exact (eq_refl (term68 K k i)). Qed.
Lemma lem4467147 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term85 A K k t s i) = (term85 A K k t s i).
Proof. exact (MK_COMB (@lem4467146 K k i) (@lem4467143 A K t s i)). Qed.
Lemma lem4467148 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term86 A K k t s) = (term86 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467147 A K k t s i)). Qed.
Lemma lem4467149 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467150 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term87 A K k t s) = (term87 A K k t s).
Proof. exact (MK_COMB (@lem4467149 K) (@lem4467148 A K k t s)). Qed.
Lemma lem4467155 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term73 A K t s i x) = (term73 A K t s i x).
Proof. exact (eq_refl (term73 A K t s i x)). Qed.
Lemma lem4467156 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term75 A K t s i) = (term75 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467155 A K t s i x)). Qed.
Lemma lem4467157 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467158 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term76 A K t s i) = (term76 A K t s i).
Proof. exact (MK_COMB (@lem4467157 A) (@lem4467156 A K t s i)). Qed.
Lemma lem4467161 {K : Type'} (k : K -> Prop) (i : K) : (term68 K k i) = (term68 K k i).
Proof. exact (eq_refl (term68 K k i)). Qed.
Lemma lem4467162 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term77 A K k t s i) = (term77 A K k t s i).
Proof. exact (MK_COMB (@lem4467161 K k i) (@lem4467158 A K t s i)). Qed.
Lemma lem4467163 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term78 A K k t s) = (term78 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467162 A K k t s i)). Qed.
Lemma lem4467164 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467165 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term79 A K k t s) = (term79 A K k t s).
Proof. exact (MK_COMB (@lem4467164 K) (@lem4467163 A K k t s)). Qed.
Lemma lem4467170 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term73 A K s t i x) = (term73 A K s t i x).
Proof. exact (eq_refl (term73 A K s t i x)). Qed.
Lemma lem4467171 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term75 A K s t i) = (term75 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467170 A K s t i x)). Qed.
Lemma lem4467172 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467173 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term76 A K s t i) = (term76 A K s t i).
Proof. exact (MK_COMB (@lem4467172 A) (@lem4467171 A K s t i)). Qed.
Lemma lem4467176 {K : Type'} (k : K -> Prop) (i : K) : (term68 K k i) = (term68 K k i).
Proof. exact (eq_refl (term68 K k i)). Qed.
Lemma lem4467177 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term77 A K k s t i) = (term77 A K k s t i).
Proof. exact (MK_COMB (@lem4467176 K k i) (@lem4467173 A K s t i)). Qed.
Lemma lem4467178 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term78 A K k s t) = (term78 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4467177 A K k s t i)). Qed.
Lemma lem4467179 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467180 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term79 A K k s t) = (term79 A K k s t).
Proof. exact (MK_COMB (@lem4467179 K) (@lem4467178 A K k s t)). Qed.
Lemma lem4467181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467182 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term80 A K k s t) = (term80 A K k s t).
Proof. exact (MK_COMB (@lem4467181) (@lem4467180 A K k s t)). Qed.
Lemma lem4467183 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term81 A K k t s) = (term81 A K k t s).
Proof. exact (MK_COMB (@lem4467182 A K k s t) (@lem4467165 A K k t s)). Qed.
Lemma lem4467184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4467185 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term82 A K k t s) = (term82 A K k t s).
Proof. exact (MK_COMB (@lem4467184) (@lem4467183 A K k t s)). Qed.
Lemma lem4467186 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term81 A K k t s) = (term87 A K k t s)) = ((term81 A K k t s) = (term87 A K k t s)).
Proof. exact (MK_COMB (@lem4467185 A K k t s) (@lem4467150 A K k t s)). Qed.
Lemma lem4467187 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term88 A K k s) = (term88 A K k s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4467186 A K k t s)). Qed.
Lemma lem4467188 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4467189 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term89 A K k s) = (term89 A K k s).
Proof. exact (MK_COMB (@lem4467188 A K) (@lem4467187 A K k s)). Qed.
Lemma lem4467190 {A K : Type'} (k : K -> Prop) : (term90 A K k) = (term90 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4467189 A K k s)). Qed.
Lemma lem4467191 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4467192 {A K : Type'} (k : K -> Prop) : (term91 A K k) = (term91 A K k).
Proof. exact (MK_COMB (@lem4467191 A K) (@lem4467190 A K k)). Qed.
Lemma lem4467193 {A K : Type'} : (term92 A K) = (term92 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4467192 A K k)). Qed.
Lemma lem4467194 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4467195 {A K : Type'} : (term93 A K) = (term93 A K).
Proof. exact (MK_COMB (@lem4467194 K) (@lem4467193 A K)). Qed.
Lemma lem4467276 {A K : Type'} : (term95 A K) = (term93 A K).
Proof. exact (TRANS (@lem4467124 A K) (@lem4467195 A K)). Qed.
Lemma lem4467277 {A K : Type'} : (term93 A K) = (term95 A K).
Proof. exact (SYM (@lem4467276 A K)). Qed.
Lemma lem4467279 (p : Prop) : p = (term94 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4467280 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term81 A K k t s) = (term87 A K k t s)) = (term102 A K k t s).
Proof. exact (@lem4467279 ((term81 A K k t s) = (term87 A K k t s))). Qed.
Lemma lem4467281 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term102 A K k t s) = ((term81 A K k t s) = (term87 A K k t s)).
Proof. exact (SYM (@lem4467280 A K k t s)). Qed.
Lemma lem4467282 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term103 A K k t s) : term103 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4467293 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term104 A K s t i x) = (term105 A K s t i x).
Proof. exact (@lem17362 (s i x) (t i x)). Qed.
Lemma lem4467298 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term73 A K s t i x) = (term106 A K s t i x).
Proof. exact (@lem17265 (s i x) (t i x)). Qed.
Lemma lem4467299 {A : Type'} (P : A -> Prop) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4467300 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term109 A K s t i) = (term110 A K s t i).
Proof. exact (@lem4467299 A (term75 A K s t i)). Qed.
Lemma lem4467301 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term111 A K s t i x) = (term73 A K s t i x).
Proof. exact (eq_refl (term111 A K s t i x)). Qed.
Lemma lem4467302 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467303 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term112 A K s t i x) = (term104 A K s t i x).
Proof. exact (MK_COMB (@lem4467302) (@lem4467301 A K s t i x)). Qed.
Lemma lem4467304 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term112 A K s t i x) = (term105 A K s t i x).
Proof. exact (TRANS (@lem4467303 A K s t i x) (@lem4467293 A K s t i x)). Qed.
Lemma lem4467305 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term113 A K s t i) = (term114 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467304 A K s t i x)). Qed.
Lemma lem4467306 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4467307 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term110 A K s t i) = (term115 A K s t i).
Proof. exact (MK_COMB (@lem4467306 A) (@lem4467305 A K s t i)). Qed.
Lemma lem4467308 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term109 A K s t i) = (term115 A K s t i).
Proof. exact (TRANS (@lem4467300 A K s t i) (@lem4467307 A K s t i)). Qed.
Lemma lem4467309 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term75 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467298 A K s t i x)). Qed.
Lemma lem4467310 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467311 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term76 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4467310 A) (@lem4467309 A K s t i)). Qed.
Lemma lem4467313 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4467314 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term119 A K k s t i) = (term120 A K k s t i).
Proof. exact (MK_COMB (@lem4467313 K k i) (@lem4467308 A K s t i)). Qed.
Lemma lem4467315 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term121 A K k s t i) = (term119 A K k s t i).
Proof. exact (@lem17362 (k i) (term76 A K s t i)). Qed.
Lemma lem4467316 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term121 A K k s t i) = (term120 A K k s t i).
Proof. exact (TRANS (@lem4467315 A K k s t i) (@lem4467314 A K k s t i)). Qed.
Lemma lem4467318 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4467319 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term123 A K k s t i) = (term124 A K k s t i).
Proof. exact (MK_COMB (@lem4467318 K k i) (@lem4467311 A K s t i)). Qed.
Lemma lem4467320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term77 A K k s t i) = (term123 A K k s t i).
Proof. exact (@lem17265 (k i) (term76 A K s t i)). Qed.
Lemma lem4467321 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term77 A K k s t i) = (term124 A K k s t i).
Proof. exact (TRANS (@lem4467320 A K k s t i) (@lem4467319 A K k s t i)). Qed.
Lemma lem4467322 {K : Type'} (P : K -> Prop) : (term107 K P) = (term108 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4467323 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term125 A K k s t) = (term126 A K k s t).
Proof. exact (@lem4467322 K (term78 A K k s t)). Qed.
Lemma lem4467324 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term127 A K k s t i) = (term77 A K k s t i).
Proof. exact (eq_refl (term127 A K k s t i)). Qed.
Lemma lem4467325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467326 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term128 A K k s t i) = (term121 A K k s t i).
Proof. exact (MK_COMB (@lem4467325) (@lem4467324 A K k s t i)). Qed.
Lemma lem4467327 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term128 A K k s t i) = (term120 A K k s t i).
Proof. exact (TRANS (@lem4467326 A K k s t i) (@lem4467316 A K k s t i)). Qed.
Lemma lem4467328 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term129 A K k s t) = (term130 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4467327 A K k s t i)). Qed.
Lemma lem4467329 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4467330 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term126 A K k s t) = (term131 A K k s t).
Proof. exact (MK_COMB (@lem4467329 K) (@lem4467328 A K k s t)). Qed.
Lemma lem4467331 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term125 A K k s t) = (term131 A K k s t).
Proof. exact (TRANS (@lem4467323 A K k s t) (@lem4467330 A K k s t)). Qed.
Lemma lem4467332 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term78 A K k s t) = (term132 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4467321 A K k s t i)). Qed.
Lemma lem4467333 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467334 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term79 A K k s t) = (term133 A K k s t).
Proof. exact (MK_COMB (@lem4467333 K) (@lem4467332 A K k s t)). Qed.
Lemma lem4467345 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term104 A K t s i x) = (term105 A K t s i x).
Proof. exact (@lem17362 (t i x) (s i x)). Qed.
Lemma lem4467350 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term73 A K t s i x) = (term106 A K t s i x).
Proof. exact (@lem17265 (t i x) (s i x)). Qed.
Lemma lem4467351 {A : Type'} (P : A -> Prop) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4467352 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term109 A K t s i) = (term110 A K t s i).
Proof. exact (@lem4467351 A (term75 A K t s i)). Qed.
Lemma lem4467353 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term111 A K t s i x) = (term73 A K t s i x).
Proof. exact (eq_refl (term111 A K t s i x)). Qed.
Lemma lem4467354 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467355 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term112 A K t s i x) = (term104 A K t s i x).
Proof. exact (MK_COMB (@lem4467354) (@lem4467353 A K t s i x)). Qed.
Lemma lem4467356 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term112 A K t s i x) = (term105 A K t s i x).
Proof. exact (TRANS (@lem4467355 A K t s i x) (@lem4467345 A K t s i x)). Qed.
Lemma lem4467357 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term113 A K t s i) = (term114 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467356 A K t s i x)). Qed.
Lemma lem4467358 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4467359 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term110 A K t s i) = (term115 A K t s i).
Proof. exact (MK_COMB (@lem4467358 A) (@lem4467357 A K t s i)). Qed.
Lemma lem4467360 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term109 A K t s i) = (term115 A K t s i).
Proof. exact (TRANS (@lem4467352 A K t s i) (@lem4467359 A K t s i)). Qed.
Lemma lem4467361 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term75 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467350 A K t s i x)). Qed.
Lemma lem4467362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467363 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term76 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4467362 A) (@lem4467361 A K t s i)). Qed.
Lemma lem4467365 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4467366 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term119 A K k t s i) = (term120 A K k t s i).
Proof. exact (MK_COMB (@lem4467365 K k i) (@lem4467360 A K t s i)). Qed.
Lemma lem4467367 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term121 A K k t s i) = (term119 A K k t s i).
Proof. exact (@lem17362 (k i) (term76 A K t s i)). Qed.
Lemma lem4467368 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term121 A K k t s i) = (term120 A K k t s i).
Proof. exact (TRANS (@lem4467367 A K k t s i) (@lem4467366 A K k t s i)). Qed.
Lemma lem4467370 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4467371 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term123 A K k t s i) = (term124 A K k t s i).
Proof. exact (MK_COMB (@lem4467370 K k i) (@lem4467363 A K t s i)). Qed.
Lemma lem4467372 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term77 A K k t s i) = (term123 A K k t s i).
Proof. exact (@lem17265 (k i) (term76 A K t s i)). Qed.
Lemma lem4467373 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term77 A K k t s i) = (term124 A K k t s i).
Proof. exact (TRANS (@lem4467372 A K k t s i) (@lem4467371 A K k t s i)). Qed.
Lemma lem4467374 {K : Type'} (P : K -> Prop) : (term107 K P) = (term108 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4467375 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term125 A K k t s) = (term126 A K k t s).
Proof. exact (@lem4467374 K (term78 A K k t s)). Qed.
Lemma lem4467376 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term127 A K k t s i) = (term77 A K k t s i).
Proof. exact (eq_refl (term127 A K k t s i)). Qed.
Lemma lem4467377 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467378 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term128 A K k t s i) = (term121 A K k t s i).
Proof. exact (MK_COMB (@lem4467377) (@lem4467376 A K k t s i)). Qed.
Lemma lem4467379 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term128 A K k t s i) = (term120 A K k t s i).
Proof. exact (TRANS (@lem4467378 A K k t s i) (@lem4467368 A K k t s i)). Qed.
Lemma lem4467380 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term129 A K k t s) = (term130 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467379 A K k t s i)). Qed.
Lemma lem4467381 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4467382 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term126 A K k t s) = (term131 A K k t s).
Proof. exact (MK_COMB (@lem4467381 K) (@lem4467380 A K k t s)). Qed.
Lemma lem4467383 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term125 A K k t s) = (term131 A K k t s).
Proof. exact (TRANS (@lem4467375 A K k t s) (@lem4467382 A K k t s)). Qed.
Lemma lem4467384 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term78 A K k t s) = (term132 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467373 A K k t s i)). Qed.
Lemma lem4467385 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467386 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term79 A K k t s) = (term133 A K k t s).
Proof. exact (MK_COMB (@lem4467385 K) (@lem4467384 A K k t s)). Qed.
Lemma lem4467387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4467388 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term134 A K k s t) = (term135 A K k s t).
Proof. exact (MK_COMB (@lem4467387) (@lem4467331 A K k s t)). Qed.
Lemma lem4467389 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term136 A K k t s) = (term137 A K k t s).
Proof. exact (MK_COMB (@lem4467388 A K k s t) (@lem4467383 A K k t s)). Qed.
Lemma lem4467390 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term138 A K k t s) = (term136 A K k t s).
Proof. exact (@lem17045 (term79 A K k s t) (term79 A K k t s)). Qed.
Lemma lem4467391 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term138 A K k t s) = (term137 A K k t s).
Proof. exact (TRANS (@lem4467390 A K k t s) (@lem4467389 A K k t s)). Qed.
Lemma lem4467392 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467393 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term80 A K k s t) = (term139 A K k s t).
Proof. exact (MK_COMB (@lem4467392) (@lem4467334 A K k s t)). Qed.
Lemma lem4467394 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term81 A K k t s) = (term140 A K k t s).
Proof. exact (MK_COMB (@lem4467393 A K k s t) (@lem4467386 A K k t s)). Qed.
Lemma lem4467405 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term104 A K s t i x) = (term105 A K s t i x).
Proof. exact (@lem17362 (s i x) (t i x)). Qed.
Lemma lem4467410 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term73 A K s t i x) = (term106 A K s t i x).
Proof. exact (@lem17265 (s i x) (t i x)). Qed.
Lemma lem4467411 {A : Type'} (P : A -> Prop) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4467412 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term109 A K s t i) = (term110 A K s t i).
Proof. exact (@lem4467411 A (term75 A K s t i)). Qed.
Lemma lem4467413 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term111 A K s t i x) = (term73 A K s t i x).
Proof. exact (eq_refl (term111 A K s t i x)). Qed.
Lemma lem4467414 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467415 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term112 A K s t i x) = (term104 A K s t i x).
Proof. exact (MK_COMB (@lem4467414) (@lem4467413 A K s t i x)). Qed.
Lemma lem4467416 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term112 A K s t i x) = (term105 A K s t i x).
Proof. exact (TRANS (@lem4467415 A K s t i x) (@lem4467405 A K s t i x)). Qed.
Lemma lem4467417 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term113 A K s t i) = (term114 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467416 A K s t i x)). Qed.
Lemma lem4467418 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4467419 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term110 A K s t i) = (term115 A K s t i).
Proof. exact (MK_COMB (@lem4467418 A) (@lem4467417 A K s t i)). Qed.
Lemma lem4467420 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term109 A K s t i) = (term115 A K s t i).
Proof. exact (TRANS (@lem4467412 A K s t i) (@lem4467419 A K s t i)). Qed.
Lemma lem4467421 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term75 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4467410 A K s t i x)). Qed.
Lemma lem4467422 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467423 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term76 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4467422 A) (@lem4467421 A K s t i)). Qed.
Lemma lem4467432 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term104 A K t s i x) = (term105 A K t s i x).
Proof. exact (@lem17362 (t i x) (s i x)). Qed.
Lemma lem4467437 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term73 A K t s i x) = (term106 A K t s i x).
Proof. exact (@lem17265 (t i x) (s i x)). Qed.
Lemma lem4467438 {A : Type'} (P : A -> Prop) : (term107 A P) = (term108 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4467439 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term109 A K t s i) = (term110 A K t s i).
Proof. exact (@lem4467438 A (term75 A K t s i)). Qed.
Lemma lem4467440 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term111 A K t s i x) = (term73 A K t s i x).
Proof. exact (eq_refl (term111 A K t s i x)). Qed.
Lemma lem4467441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467442 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term112 A K t s i x) = (term104 A K t s i x).
Proof. exact (MK_COMB (@lem4467441) (@lem4467440 A K t s i x)). Qed.
Lemma lem4467443 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term112 A K t s i x) = (term105 A K t s i x).
Proof. exact (TRANS (@lem4467442 A K t s i x) (@lem4467432 A K t s i x)). Qed.
Lemma lem4467444 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term113 A K t s i) = (term114 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467443 A K t s i x)). Qed.
Lemma lem4467445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4467446 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term110 A K t s i) = (term115 A K t s i).
Proof. exact (MK_COMB (@lem4467445 A) (@lem4467444 A K t s i)). Qed.
Lemma lem4467447 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term109 A K t s i) = (term115 A K t s i).
Proof. exact (TRANS (@lem4467439 A K t s i) (@lem4467446 A K t s i)). Qed.
Lemma lem4467448 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term75 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4467437 A K t s i x)). Qed.
Lemma lem4467449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4467450 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term76 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4467449 A) (@lem4467448 A K t s i)). Qed.
Lemma lem4467451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4467452 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term141 A K s t i) = (term142 A K s t i).
Proof. exact (MK_COMB (@lem4467451) (@lem4467420 A K s t i)). Qed.
Lemma lem4467453 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term143 A K t s i) = (term144 A K t s i).
Proof. exact (MK_COMB (@lem4467452 A K s t i) (@lem4467447 A K t s i)). Qed.
Lemma lem4467454 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term145 A K t s i) = (term143 A K t s i).
Proof. exact (@lem17045 (term76 A K s t i) (term76 A K t s i)). Qed.
Lemma lem4467455 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term145 A K t s i) = (term144 A K t s i).
Proof. exact (TRANS (@lem4467454 A K t s i) (@lem4467453 A K t s i)). Qed.
Lemma lem4467456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467457 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term83 A K s t i) = (term146 A K s t i).
Proof. exact (MK_COMB (@lem4467456) (@lem4467423 A K s t i)). Qed.
Lemma lem4467458 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term84 A K t s i) = (term147 A K t s i).
Proof. exact (MK_COMB (@lem4467457 A K s t i) (@lem4467450 A K t s i)). Qed.
Lemma lem4467460 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4467461 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term148 A K k t s i) = (term149 A K k t s i).
Proof. exact (MK_COMB (@lem4467460 K k i) (@lem4467455 A K t s i)). Qed.
Lemma lem4467462 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term150 A K k t s i) = (term148 A K k t s i).
Proof. exact (@lem17362 (k i) (term84 A K t s i)). Qed.
Lemma lem4467463 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term150 A K k t s i) = (term149 A K k t s i).
Proof. exact (TRANS (@lem4467462 A K k t s i) (@lem4467461 A K k t s i)). Qed.
Lemma lem4467465 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4467466 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term151 A K k t s i) = (term152 A K k t s i).
Proof. exact (MK_COMB (@lem4467465 K k i) (@lem4467458 A K t s i)). Qed.
Lemma lem4467467 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term85 A K k t s i) = (term151 A K k t s i).
Proof. exact (@lem17265 (k i) (term84 A K t s i)). Qed.
Lemma lem4467468 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term85 A K k t s i) = (term152 A K k t s i).
Proof. exact (TRANS (@lem4467467 A K k t s i) (@lem4467466 A K k t s i)). Qed.
Lemma lem4467469 {K : Type'} (P : K -> Prop) : (term107 K P) = (term108 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4467470 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term153 A K k t s) = (term154 A K k t s).
Proof. exact (@lem4467469 K (term86 A K k t s)). Qed.
Lemma lem4467471 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term155 A K k t s i) = (term85 A K k t s i).
Proof. exact (eq_refl (term155 A K k t s i)). Qed.
Lemma lem4467472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4467473 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term156 A K k t s i) = (term150 A K k t s i).
Proof. exact (MK_COMB (@lem4467472) (@lem4467471 A K k t s i)). Qed.
Lemma lem4467474 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term156 A K k t s i) = (term149 A K k t s i).
Proof. exact (TRANS (@lem4467473 A K k t s i) (@lem4467463 A K k t s i)). Qed.
Lemma lem4467475 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term157 A K k t s) = (term158 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467474 A K k t s i)). Qed.
Lemma lem4467476 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4467477 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term154 A K k t s) = (term159 A K k t s).
Proof. exact (MK_COMB (@lem4467476 K) (@lem4467475 A K k t s)). Qed.
Lemma lem4467478 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term153 A K k t s) = (term159 A K k t s).
Proof. exact (TRANS (@lem4467470 A K k t s) (@lem4467477 A K k t s)). Qed.
Lemma lem4467479 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term86 A K k t s) = (term160 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4467468 A K k t s i)). Qed.
Lemma lem4467480 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4467481 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term87 A K k t s) = (term161 A K k t s).
Proof. exact (MK_COMB (@lem4467480 K) (@lem4467479 A K k t s)). Qed.
Lemma lem4467482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467483 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term162 A K k t s) = (term163 A K k t s).
Proof. exact (MK_COMB (@lem4467482) (@lem4467391 A K k t s)). Qed.
Lemma lem4467484 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term164 A K k t s) = (term165 A K k t s).
Proof. exact (MK_COMB (@lem4467483 A K k t s) (@lem4467481 A K k t s)). Qed.
Lemma lem4467485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4467486 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term166 A K k t s) = (term167 A K k t s).
Proof. exact (MK_COMB (@lem4467485) (@lem4467394 A K k t s)). Qed.
Lemma lem4467487 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term168 A K k t s) = (term169 A K k t s).
Proof. exact (MK_COMB (@lem4467486 A K k t s) (@lem4467478 A K k t s)). Qed.
Lemma lem4467488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4467489 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term170 A K k t s) = (term171 A K k t s).
Proof. exact (MK_COMB (@lem4467488) (@lem4467487 A K k t s)). Qed.
Lemma lem4467490 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term172 A K k t s) = (term173 A K k t s).
Proof. exact (MK_COMB (@lem4467489 A K k t s) (@lem4467484 A K k t s)). Qed.
Lemma lem4467491 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term103 A K k t s) = (term172 A K k t s).
Proof. exact (@lem17646 (term81 A K k t s) (term87 A K k t s)). Qed.
Lemma lem4467492 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term103 A K k t s) = (term173 A K k t s).
Proof. exact (TRANS (@lem4467491 A K k t s) (@lem4467490 A K k t s)). Qed.
Lemma lem4468107 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4468108 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (@lem4468107 A P Q). Qed.
Lemma lem4468109 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term176 A K t s i) = (term177 A K t s i).
Proof. exact (@lem4468108 A (term114 A K s t i) (term114 A K t s i)). Qed.
Lemma lem4468110 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term178 A K s t i x) = (term105 A K s t i x).
Proof. exact (eq_refl (term178 A K s t i x)). Qed.
Lemma lem4468111 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term179 A K s t i) = (term114 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468110 A K s t i x)). Qed.
Lemma lem4468112 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468113 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term180 A K s t i) = (term115 A K s t i).
Proof. exact (MK_COMB (@lem4468112 A) (@lem4468111 A K s t i)). Qed.
Lemma lem4468114 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468115 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term181 A K s t i) = (term142 A K s t i).
Proof. exact (MK_COMB (@lem4468114) (@lem4468113 A K s t i)). Qed.
Lemma lem4468116 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term178 A K t s i x) = (term105 A K t s i x).
Proof. exact (eq_refl (term178 A K t s i x)). Qed.
Lemma lem4468117 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term179 A K t s i) = (term114 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468116 A K t s i x)). Qed.
Lemma lem4468118 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468119 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term180 A K t s i) = (term115 A K t s i).
Proof. exact (MK_COMB (@lem4468118 A) (@lem4468117 A K t s i)). Qed.
Lemma lem4468120 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term176 A K t s i) = (term144 A K t s i).
Proof. exact (MK_COMB (@lem4468115 A K s t i) (@lem4468119 A K t s i)). Qed.
Lemma lem4468121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468122 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term182 A K t s i) = (term183 A K t s i).
Proof. exact (MK_COMB (@lem4468121) (@lem4468120 A K t s i)). Qed.
Lemma lem4468123 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term178 A K s t i x) = (term105 A K s t i x).
Proof. exact (eq_refl (term178 A K s t i x)). Qed.
Lemma lem4468124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468125 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term184 A K s t i x) = (term185 A K s t i x).
Proof. exact (MK_COMB (@lem4468124) (@lem4468123 A K s t i x)). Qed.
Lemma lem4468126 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term178 A K t s i x) = (term105 A K t s i x).
Proof. exact (eq_refl (term178 A K t s i x)). Qed.
Lemma lem4468127 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term186 A K t s i x) = (term187 A K t s i x).
Proof. exact (MK_COMB (@lem4468125 A K s t i x) (@lem4468126 A K t s i x)). Qed.
Lemma lem4468128 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term188 A K t s i) = (term189 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468127 A K t s i x)). Qed.
Lemma lem4468129 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468130 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term177 A K t s i) = (term190 A K t s i).
Proof. exact (MK_COMB (@lem4468129 A) (@lem4468128 A K t s i)). Qed.
Lemma lem4468131 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : ((term176 A K t s i) = (term177 A K t s i)) = ((term144 A K t s i) = (term190 A K t s i)).
Proof. exact (MK_COMB (@lem4468122 A K t s i) (@lem4468130 A K t s i)). Qed.
Lemma lem4468132 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term144 A K t s i) = (term190 A K t s i).
Proof. exact (EQ_MP (@lem4468131 A K t s i) (@lem4468109 A K t s i)). Qed.
Lemma lem4468133 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468134 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term149 A K k t s i) = (term191 A K k t s i).
Proof. exact (MK_COMB (@lem4468133 K k i) (@lem4468132 A K t s i)). Qed.
Lemma lem4468136 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4468137 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem4468136 A P Q). Qed.
Lemma lem4468138 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term194 A K k t s i) = (term195 A K k t s i).
Proof. exact (@lem4468137 A (k i) (term189 A K t s i)). Qed.
Lemma lem4468139 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term196 A K t s i x) = (term187 A K t s i x).
Proof. exact (eq_refl (term196 A K t s i x)). Qed.
Lemma lem4468140 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term197 A K t s i) = (term189 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468139 A K t s i x)). Qed.
Lemma lem4468141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468142 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term198 A K t s i) = (term190 A K t s i).
Proof. exact (MK_COMB (@lem4468141 A) (@lem4468140 A K t s i)). Qed.
Lemma lem4468143 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468144 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term194 A K k t s i) = (term191 A K k t s i).
Proof. exact (MK_COMB (@lem4468143 K k i) (@lem4468142 A K t s i)). Qed.
Lemma lem4468145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468146 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term199 A K k t s i) = (term200 A K k t s i).
Proof. exact (MK_COMB (@lem4468145) (@lem4468144 A K k t s i)). Qed.
Lemma lem4468147 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term196 A K t s i x) = (term187 A K t s i x).
Proof. exact (eq_refl (term196 A K t s i x)). Qed.
Lemma lem4468148 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468149 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term201 A K k t s i x) = (term202 A K k t s i x).
Proof. exact (MK_COMB (@lem4468148 K k i) (@lem4468147 A K t s i x)). Qed.
Lemma lem4468150 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term203 A K k t s i) = (term204 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468149 A K k t s i x)). Qed.
Lemma lem4468151 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468152 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term195 A K k t s i) = (term205 A K k t s i).
Proof. exact (MK_COMB (@lem4468151 A) (@lem4468150 A K k t s i)). Qed.
Lemma lem4468153 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term194 A K k t s i) = (term195 A K k t s i)) = ((term191 A K k t s i) = (term205 A K k t s i)).
Proof. exact (MK_COMB (@lem4468146 A K k t s i) (@lem4468152 A K k t s i)). Qed.
Lemma lem4468154 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term191 A K k t s i) = (term205 A K k t s i).
Proof. exact (EQ_MP (@lem4468153 A K k t s i) (@lem4468138 A K k t s i)). Qed.
Lemma lem4468155 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term149 A K k t s i) = (term205 A K k t s i).
Proof. exact (TRANS (@lem4468134 A K k t s i) (@lem4468154 A K k t s i)). Qed.
Lemma lem4468156 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term158 A K k t s) = (term206 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468155 A K k t s i)). Qed.
Lemma lem4468157 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468158 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term159 A K k t s) = (term207 A K k t s).
Proof. exact (MK_COMB (@lem4468157 K) (@lem4468156 A K k t s)). Qed.
Lemma lem4468159 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (eq_refl (term167 A K k t s)). Qed.
Lemma lem4468160 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term169 A K k t s) = (term208 A K k t s).
Proof. exact (MK_COMB (@lem4468159 A K k t s) (@lem4468158 A K k t s)). Qed.
Lemma lem4468162 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4468163 {K : Type'} (P : Prop) (Q : K -> Prop) : (term192 K P Q) = (term193 K P Q).
Proof. exact (@lem4468162 K P Q). Qed.
Lemma lem4468164 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term209 A K k t s) = (term210 A K k t s).
Proof. exact (@lem4468163 K (term140 A K k t s) (term206 A K k t s)). Qed.
Lemma lem4468165 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term211 A K k t s i) = (term205 A K k t s i).
Proof. exact (eq_refl (term211 A K k t s i)). Qed.
Lemma lem4468166 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term212 A K k t s) = (term206 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468165 A K k t s i)). Qed.
Lemma lem4468167 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468168 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term213 A K k t s) = (term207 A K k t s).
Proof. exact (MK_COMB (@lem4468167 K) (@lem4468166 A K k t s)). Qed.
Lemma lem4468169 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (eq_refl (term167 A K k t s)). Qed.
Lemma lem4468170 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term209 A K k t s) = (term208 A K k t s).
Proof. exact (MK_COMB (@lem4468169 A K k t s) (@lem4468168 A K k t s)). Qed.
Lemma lem4468171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468172 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term214 A K k t s) = (term215 A K k t s).
Proof. exact (MK_COMB (@lem4468171) (@lem4468170 A K k t s)). Qed.
Lemma lem4468173 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term211 A K k t s i) = (term205 A K k t s i).
Proof. exact (eq_refl (term211 A K k t s i)). Qed.
Lemma lem4468174 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (eq_refl (term167 A K k t s)). Qed.
Lemma lem4468175 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term216 A K k t s i) = (term217 A K k t s i).
Proof. exact (MK_COMB (@lem4468174 A K k t s) (@lem4468173 A K k t s i)). Qed.
Lemma lem4468176 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term218 A K k t s) = (term219 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468175 A K k t s i)). Qed.
Lemma lem4468177 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468178 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term210 A K k t s) = (term220 A K k t s).
Proof. exact (MK_COMB (@lem4468177 K) (@lem4468176 A K k t s)). Qed.
Lemma lem4468179 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term209 A K k t s) = (term210 A K k t s)) = ((term208 A K k t s) = (term220 A K k t s)).
Proof. exact (MK_COMB (@lem4468172 A K k t s) (@lem4468178 A K k t s)). Qed.
Lemma lem4468180 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term208 A K k t s) = (term220 A K k t s).
Proof. exact (EQ_MP (@lem4468179 A K k t s) (@lem4468164 A K k t s)). Qed.
Lemma lem4468182 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4468183 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem4468182 A P Q). Qed.
Lemma lem4468184 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term221 A K k t s i) = (term222 A K k t s i).
Proof. exact (@lem4468183 A (term140 A K k t s) (term204 A K k t s i)). Qed.
Lemma lem4468185 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term223 A K k t s i x) = (term202 A K k t s i x).
Proof. exact (eq_refl (term223 A K k t s i x)). Qed.
Lemma lem4468186 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term224 A K k t s i) = (term204 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468185 A K k t s i x)). Qed.
Lemma lem4468187 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468188 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term225 A K k t s i) = (term205 A K k t s i).
Proof. exact (MK_COMB (@lem4468187 A) (@lem4468186 A K k t s i)). Qed.
Lemma lem4468189 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (eq_refl (term167 A K k t s)). Qed.
Lemma lem4468190 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term221 A K k t s i) = (term217 A K k t s i).
Proof. exact (MK_COMB (@lem4468189 A K k t s) (@lem4468188 A K k t s i)). Qed.
Lemma lem4468191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468192 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term226 A K k t s i) = (term227 A K k t s i).
Proof. exact (MK_COMB (@lem4468191) (@lem4468190 A K k t s i)). Qed.
Lemma lem4468193 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term223 A K k t s i x) = (term202 A K k t s i x).
Proof. exact (eq_refl (term223 A K k t s i x)). Qed.
Lemma lem4468194 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (eq_refl (term167 A K k t s)). Qed.
Lemma lem4468195 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term228 A K k t s i x) = (term229 A K k t s i x).
Proof. exact (MK_COMB (@lem4468194 A K k t s) (@lem4468193 A K k t s i x)). Qed.
Lemma lem4468196 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term230 A K k t s i) = (term231 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468195 A K k t s i x)). Qed.
Lemma lem4468197 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468198 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term222 A K k t s i) = (term232 A K k t s i).
Proof. exact (MK_COMB (@lem4468197 A) (@lem4468196 A K k t s i)). Qed.
Lemma lem4468199 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term221 A K k t s i) = (term222 A K k t s i)) = ((term217 A K k t s i) = (term232 A K k t s i)).
Proof. exact (MK_COMB (@lem4468192 A K k t s i) (@lem4468198 A K k t s i)). Qed.
Lemma lem4468200 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term217 A K k t s i) = (term232 A K k t s i).
Proof. exact (EQ_MP (@lem4468199 A K k t s i) (@lem4468184 A K k t s i)). Qed.
Lemma lem4468201 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term219 A K k t s) = (term233 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468200 A K k t s i)). Qed.
Lemma lem4468202 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468203 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term220 A K k t s) = (term234 A K k t s).
Proof. exact (MK_COMB (@lem4468202 K) (@lem4468201 A K k t s)). Qed.
Lemma lem4468204 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term208 A K k t s) = (term234 A K k t s).
Proof. exact (TRANS (@lem4468180 A K k t s) (@lem4468203 A K k t s)). Qed.
Lemma lem4468205 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term169 A K k t s) = (term234 A K k t s).
Proof. exact (TRANS (@lem4468160 A K k t s) (@lem4468204 A K k t s)). Qed.
Lemma lem4468206 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468207 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term171 A K k t s) = (term235 A K k t s).
Proof. exact (MK_COMB (@lem4468206) (@lem4468205 A K k t s)). Qed.
Lemma lem4468209 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4468210 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem4468209 A P Q). Qed.
Lemma lem4468211 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term236 A K k s t i) = (term237 A K k s t i).
Proof. exact (@lem4468210 A (k i) (term114 A K s t i)). Qed.
Lemma lem4468212 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term178 A K s t i x) = (term105 A K s t i x).
Proof. exact (eq_refl (term178 A K s t i x)). Qed.
Lemma lem4468213 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term179 A K s t i) = (term114 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468212 A K s t i x)). Qed.
Lemma lem4468214 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468215 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term180 A K s t i) = (term115 A K s t i).
Proof. exact (MK_COMB (@lem4468214 A) (@lem4468213 A K s t i)). Qed.
Lemma lem4468216 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468217 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term236 A K k s t i) = (term120 A K k s t i).
Proof. exact (MK_COMB (@lem4468216 K k i) (@lem4468215 A K s t i)). Qed.
Lemma lem4468218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468219 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term238 A K k s t i) = (term239 A K k s t i).
Proof. exact (MK_COMB (@lem4468218) (@lem4468217 A K k s t i)). Qed.
Lemma lem4468220 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term178 A K s t i x) = (term105 A K s t i x).
Proof. exact (eq_refl (term178 A K s t i x)). Qed.
Lemma lem4468221 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468222 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term240 A K k s t i x) = (term241 A K k s t i x).
Proof. exact (MK_COMB (@lem4468221 K k i) (@lem4468220 A K s t i x)). Qed.
Lemma lem4468223 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term242 A K k s t i) = (term243 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4468222 A K k s t i x)). Qed.
Lemma lem4468224 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468225 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term237 A K k s t i) = (term244 A K k s t i).
Proof. exact (MK_COMB (@lem4468224 A) (@lem4468223 A K k s t i)). Qed.
Lemma lem4468226 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term236 A K k s t i) = (term237 A K k s t i)) = ((term120 A K k s t i) = (term244 A K k s t i)).
Proof. exact (MK_COMB (@lem4468219 A K k s t i) (@lem4468225 A K k s t i)). Qed.
Lemma lem4468227 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term120 A K k s t i) = (term244 A K k s t i).
Proof. exact (EQ_MP (@lem4468226 A K k s t i) (@lem4468211 A K k s t i)). Qed.
Lemma lem4468228 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term130 A K k s t) = (term245 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4468227 A K k s t i)). Qed.
Lemma lem4468229 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468230 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term131 A K k s t) = (term246 A K k s t).
Proof. exact (MK_COMB (@lem4468229 K) (@lem4468228 A K k s t)). Qed.
Lemma lem4468231 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468232 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term135 A K k s t) = (term247 A K k s t).
Proof. exact (MK_COMB (@lem4468231) (@lem4468230 A K k s t)). Qed.
Lemma lem4468234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4468235 {A : Type'} (P : Prop) (Q : A -> Prop) : (term192 A P Q) = (term193 A P Q).
Proof. exact (@lem4468234 A P Q). Qed.
Lemma lem4468236 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term236 A K k t s i) = (term237 A K k t s i).
Proof. exact (@lem4468235 A (k i) (term114 A K t s i)). Qed.
Lemma lem4468237 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term178 A K t s i x) = (term105 A K t s i x).
Proof. exact (eq_refl (term178 A K t s i x)). Qed.
Lemma lem4468238 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term179 A K t s i) = (term114 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468237 A K t s i x)). Qed.
Lemma lem4468239 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468240 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term180 A K t s i) = (term115 A K t s i).
Proof. exact (MK_COMB (@lem4468239 A) (@lem4468238 A K t s i)). Qed.
Lemma lem4468241 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468242 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term236 A K k t s i) = (term120 A K k t s i).
Proof. exact (MK_COMB (@lem4468241 K k i) (@lem4468240 A K t s i)). Qed.
Lemma lem4468243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468244 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term238 A K k t s i) = (term239 A K k t s i).
Proof. exact (MK_COMB (@lem4468243) (@lem4468242 A K k t s i)). Qed.
Lemma lem4468245 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term178 A K t s i x) = (term105 A K t s i x).
Proof. exact (eq_refl (term178 A K t s i x)). Qed.
Lemma lem4468246 {K : Type'} (k : K -> Prop) (i : K) : (term118 K k i) = (term118 K k i).
Proof. exact (eq_refl (term118 K k i)). Qed.
Lemma lem4468247 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term240 A K k t s i x) = (term241 A K k t s i x).
Proof. exact (MK_COMB (@lem4468246 K k i) (@lem4468245 A K t s i x)). Qed.
Lemma lem4468248 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term242 A K k t s i) = (term243 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468247 A K k t s i x)). Qed.
Lemma lem4468249 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468250 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term237 A K k t s i) = (term244 A K k t s i).
Proof. exact (MK_COMB (@lem4468249 A) (@lem4468248 A K k t s i)). Qed.
Lemma lem4468251 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term236 A K k t s i) = (term237 A K k t s i)) = ((term120 A K k t s i) = (term244 A K k t s i)).
Proof. exact (MK_COMB (@lem4468244 A K k t s i) (@lem4468250 A K k t s i)). Qed.
Lemma lem4468252 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term120 A K k t s i) = (term244 A K k t s i).
Proof. exact (EQ_MP (@lem4468251 A K k t s i) (@lem4468236 A K k t s i)). Qed.
Lemma lem4468253 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term130 A K k t s) = (term245 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468252 A K k t s i)). Qed.
Lemma lem4468254 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468255 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term131 A K k t s) = (term246 A K k t s).
Proof. exact (MK_COMB (@lem4468254 K) (@lem4468253 A K k t s)). Qed.
Lemma lem4468256 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term137 A K k t s) = (term248 A K k t s).
Proof. exact (MK_COMB (@lem4468232 A K k s t) (@lem4468255 A K k t s)). Qed.
Lemma lem4468258 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4468259 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term174 K P Q) = (term175 K P Q).
Proof. exact (@lem4468258 K P Q). Qed.
Lemma lem4468260 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term249 A K k t s) = (term250 A K k t s).
Proof. exact (@lem4468259 K (term245 A K k s t) (term245 A K k t s)). Qed.
Lemma lem4468261 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K k s t i) = (term244 A K k s t i).
Proof. exact (eq_refl (term251 A K k s t i)). Qed.
Lemma lem4468262 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term252 A K k s t) = (term245 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4468261 A K k s t i)). Qed.
Lemma lem4468263 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468264 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term253 A K k s t) = (term246 A K k s t).
Proof. exact (MK_COMB (@lem4468263 K) (@lem4468262 A K k s t)). Qed.
Lemma lem4468265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468266 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term254 A K k s t) = (term247 A K k s t).
Proof. exact (MK_COMB (@lem4468265) (@lem4468264 A K k s t)). Qed.
Lemma lem4468267 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term251 A K k t s i) = (term244 A K k t s i).
Proof. exact (eq_refl (term251 A K k t s i)). Qed.
Lemma lem4468268 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term252 A K k t s) = (term245 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468267 A K k t s i)). Qed.
Lemma lem4468269 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468270 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term253 A K k t s) = (term246 A K k t s).
Proof. exact (MK_COMB (@lem4468269 K) (@lem4468268 A K k t s)). Qed.
Lemma lem4468271 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term249 A K k t s) = (term248 A K k t s).
Proof. exact (MK_COMB (@lem4468266 A K k s t) (@lem4468270 A K k t s)). Qed.
Lemma lem4468272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468273 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term255 A K k t s) = (term256 A K k t s).
Proof. exact (MK_COMB (@lem4468272) (@lem4468271 A K k t s)). Qed.
Lemma lem4468274 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K k s t i) = (term244 A K k s t i).
Proof. exact (eq_refl (term251 A K k s t i)). Qed.
Lemma lem4468275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468276 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term257 A K k s t i) = (term258 A K k s t i).
Proof. exact (MK_COMB (@lem4468275) (@lem4468274 A K k s t i)). Qed.
Lemma lem4468277 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term251 A K k t s i) = (term244 A K k t s i).
Proof. exact (eq_refl (term251 A K k t s i)). Qed.
Lemma lem4468278 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term259 A K k t s i) = (term260 A K k t s i).
Proof. exact (MK_COMB (@lem4468276 A K k s t i) (@lem4468277 A K k t s i)). Qed.
Lemma lem4468279 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term261 A K k t s) = (term262 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468278 A K k t s i)). Qed.
Lemma lem4468280 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468281 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term250 A K k t s) = (term263 A K k t s).
Proof. exact (MK_COMB (@lem4468280 K) (@lem4468279 A K k t s)). Qed.
Lemma lem4468282 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term249 A K k t s) = (term250 A K k t s)) = ((term248 A K k t s) = (term263 A K k t s)).
Proof. exact (MK_COMB (@lem4468273 A K k t s) (@lem4468281 A K k t s)). Qed.
Lemma lem4468283 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term248 A K k t s) = (term263 A K k t s).
Proof. exact (EQ_MP (@lem4468282 A K k t s) (@lem4468260 A K k t s)). Qed.
Lemma lem4468285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4468286 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (@lem4468285 A P Q). Qed.
Lemma lem4468287 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term264 A K k t s i) = (term265 A K k t s i).
Proof. exact (@lem4468286 A (term243 A K k s t i) (term243 A K k t s i)). Qed.
Lemma lem4468288 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term266 A K k s t i x) = (term241 A K k s t i x).
Proof. exact (eq_refl (term266 A K k s t i x)). Qed.
Lemma lem4468289 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term267 A K k s t i) = (term243 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4468288 A K k s t i x)). Qed.
Lemma lem4468290 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468291 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term268 A K k s t i) = (term244 A K k s t i).
Proof. exact (MK_COMB (@lem4468290 A) (@lem4468289 A K k s t i)). Qed.
Lemma lem4468292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468293 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term269 A K k s t i) = (term258 A K k s t i).
Proof. exact (MK_COMB (@lem4468292) (@lem4468291 A K k s t i)). Qed.
Lemma lem4468294 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term266 A K k t s i x) = (term241 A K k t s i x).
Proof. exact (eq_refl (term266 A K k t s i x)). Qed.
Lemma lem4468295 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term267 A K k t s i) = (term243 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468294 A K k t s i x)). Qed.
Lemma lem4468296 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468297 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term268 A K k t s i) = (term244 A K k t s i).
Proof. exact (MK_COMB (@lem4468296 A) (@lem4468295 A K k t s i)). Qed.
Lemma lem4468298 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term264 A K k t s i) = (term260 A K k t s i).
Proof. exact (MK_COMB (@lem4468293 A K k s t i) (@lem4468297 A K k t s i)). Qed.
Lemma lem4468299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468300 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term270 A K k t s i) = (term271 A K k t s i).
Proof. exact (MK_COMB (@lem4468299) (@lem4468298 A K k t s i)). Qed.
Lemma lem4468301 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term266 A K k s t i x) = (term241 A K k s t i x).
Proof. exact (eq_refl (term266 A K k s t i x)). Qed.
Lemma lem4468302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468303 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term272 A K k s t i x) = (term273 A K k s t i x).
Proof. exact (MK_COMB (@lem4468302) (@lem4468301 A K k s t i x)). Qed.
Lemma lem4468304 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term266 A K k t s i x) = (term241 A K k t s i x).
Proof. exact (eq_refl (term266 A K k t s i x)). Qed.
Lemma lem4468305 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term274 A K k t s i x) = (term275 A K k t s i x).
Proof. exact (MK_COMB (@lem4468303 A K k s t i x) (@lem4468304 A K k t s i x)). Qed.
Lemma lem4468306 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term276 A K k t s i) = (term277 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468305 A K k t s i x)). Qed.
Lemma lem4468307 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468308 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term265 A K k t s i) = (term278 A K k t s i).
Proof. exact (MK_COMB (@lem4468307 A) (@lem4468306 A K k t s i)). Qed.
Lemma lem4468309 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term264 A K k t s i) = (term265 A K k t s i)) = ((term260 A K k t s i) = (term278 A K k t s i)).
Proof. exact (MK_COMB (@lem4468300 A K k t s i) (@lem4468308 A K k t s i)). Qed.
Lemma lem4468310 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term260 A K k t s i) = (term278 A K k t s i).
Proof. exact (EQ_MP (@lem4468309 A K k t s i) (@lem4468287 A K k t s i)). Qed.
Lemma lem4468311 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term262 A K k t s) = (term279 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468310 A K k t s i)). Qed.
Lemma lem4468312 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468313 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term263 A K k t s) = (term280 A K k t s).
Proof. exact (MK_COMB (@lem4468312 K) (@lem4468311 A K k t s)). Qed.
Lemma lem4468314 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term248 A K k t s) = (term280 A K k t s).
Proof. exact (TRANS (@lem4468283 A K k t s) (@lem4468313 A K k t s)). Qed.
Lemma lem4468315 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term137 A K k t s) = (term280 A K k t s).
Proof. exact (TRANS (@lem4468256 A K k t s) (@lem4468314 A K k t s)). Qed.
Lemma lem4468316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468317 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term163 A K k t s) = (term281 A K k t s).
Proof. exact (MK_COMB (@lem4468316) (@lem4468315 A K k t s)). Qed.
Lemma lem4468318 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (eq_refl (term161 A K k t s)). Qed.
Lemma lem4468319 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term165 A K k t s) = (term282 A K k t s).
Proof. exact (MK_COMB (@lem4468317 A K k t s) (@lem4468318 A K k t s)). Qed.
Lemma lem4468321 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4468322 {K : Type'} (P : K -> Prop) (Q : Prop) : (term283 K P Q) = (term284 K P Q).
Proof. exact (@lem4468321 K P Q). Qed.
Lemma lem4468323 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term285 A K k t s) = (term286 A K k t s).
Proof. exact (@lem4468322 K (term279 A K k t s) (term161 A K k t s)). Qed.
Lemma lem4468324 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term287 A K k t s i) = (term278 A K k t s i).
Proof. exact (eq_refl (term287 A K k t s i)). Qed.
Lemma lem4468325 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term288 A K k t s) = (term279 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468324 A K k t s i)). Qed.
Lemma lem4468326 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468327 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term289 A K k t s) = (term280 A K k t s).
Proof. exact (MK_COMB (@lem4468326 K) (@lem4468325 A K k t s)). Qed.
Lemma lem4468328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468329 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term290 A K k t s) = (term281 A K k t s).
Proof. exact (MK_COMB (@lem4468328) (@lem4468327 A K k t s)). Qed.
Lemma lem4468330 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (eq_refl (term161 A K k t s)). Qed.
Lemma lem4468331 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term285 A K k t s) = (term282 A K k t s).
Proof. exact (MK_COMB (@lem4468329 A K k t s) (@lem4468330 A K k t s)). Qed.
Lemma lem4468332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468333 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term291 A K k t s) = (term292 A K k t s).
Proof. exact (MK_COMB (@lem4468332) (@lem4468331 A K k t s)). Qed.
Lemma lem4468334 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term287 A K k t s i) = (term278 A K k t s i).
Proof. exact (eq_refl (term287 A K k t s i)). Qed.
Lemma lem4468335 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468336 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term293 A K k t s i) = (term294 A K k t s i).
Proof. exact (MK_COMB (@lem4468335) (@lem4468334 A K k t s i)). Qed.
Lemma lem4468337 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (eq_refl (term161 A K k t s)). Qed.
Lemma lem4468338 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term295 A K i k t s) = (term296 A K i k t s).
Proof. exact (MK_COMB (@lem4468336 A K k t s i) (@lem4468337 A K k t s)). Qed.
Lemma lem4468339 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term297 A K k t s) = (term298 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468338 A K i k t s)). Qed.
Lemma lem4468340 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468341 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term286 A K k t s) = (term299 A K k t s).
Proof. exact (MK_COMB (@lem4468340 K) (@lem4468339 A K k t s)). Qed.
Lemma lem4468342 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term285 A K k t s) = (term286 A K k t s)) = ((term282 A K k t s) = (term299 A K k t s)).
Proof. exact (MK_COMB (@lem4468333 A K k t s) (@lem4468341 A K k t s)). Qed.
Lemma lem4468343 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term282 A K k t s) = (term299 A K k t s).
Proof. exact (EQ_MP (@lem4468342 A K k t s) (@lem4468323 A K k t s)). Qed.
Lemma lem4468345 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4468346 {A : Type'} (P : A -> Prop) (Q : Prop) : (term283 A P Q) = (term284 A P Q).
Proof. exact (@lem4468345 A P Q). Qed.
Lemma lem4468347 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term300 A K i k t s) = (term301 A K i k t s).
Proof. exact (@lem4468346 A (term277 A K k t s i) (term161 A K k t s)). Qed.
Lemma lem4468348 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term302 A K k t s i x) = (term275 A K k t s i x).
Proof. exact (eq_refl (term302 A K k t s i x)). Qed.
Lemma lem4468349 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term303 A K k t s i) = (term277 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468348 A K k t s i x)). Qed.
Lemma lem4468350 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468351 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term304 A K k t s i) = (term278 A K k t s i).
Proof. exact (MK_COMB (@lem4468350 A) (@lem4468349 A K k t s i)). Qed.
Lemma lem4468352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468353 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term305 A K k t s i) = (term294 A K k t s i).
Proof. exact (MK_COMB (@lem4468352) (@lem4468351 A K k t s i)). Qed.
Lemma lem4468354 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (eq_refl (term161 A K k t s)). Qed.
Lemma lem4468355 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term300 A K i k t s) = (term296 A K i k t s).
Proof. exact (MK_COMB (@lem4468353 A K k t s i) (@lem4468354 A K k t s)). Qed.
Lemma lem4468356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468357 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term306 A K i k t s) = (term307 A K i k t s).
Proof. exact (MK_COMB (@lem4468356) (@lem4468355 A K i k t s)). Qed.
Lemma lem4468358 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term302 A K k t s i x) = (term275 A K k t s i x).
Proof. exact (eq_refl (term302 A K k t s i x)). Qed.
Lemma lem4468359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468360 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term308 A K k t s i x) = (term309 A K k t s i x).
Proof. exact (MK_COMB (@lem4468359) (@lem4468358 A K k t s i x)). Qed.
Lemma lem4468361 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (eq_refl (term161 A K k t s)). Qed.
Lemma lem4468362 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term310 A K i x k t s) = (term311 A K i x k t s).
Proof. exact (MK_COMB (@lem4468360 A K k t s i x) (@lem4468361 A K k t s)). Qed.
Lemma lem4468363 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term312 A K i k t s) = (term313 A K i k t s).
Proof. exact (fun_ext (fun x : A => @lem4468362 A K i x k t s)). Qed.
Lemma lem4468364 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468365 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term301 A K i k t s) = (term314 A K i k t s).
Proof. exact (MK_COMB (@lem4468364 A) (@lem4468363 A K i k t s)). Qed.
Lemma lem4468366 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term300 A K i k t s) = (term301 A K i k t s)) = ((term296 A K i k t s) = (term314 A K i k t s)).
Proof. exact (MK_COMB (@lem4468357 A K i k t s) (@lem4468365 A K i k t s)). Qed.
Lemma lem4468367 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term296 A K i k t s) = (term314 A K i k t s).
Proof. exact (EQ_MP (@lem4468366 A K i k t s) (@lem4468347 A K i k t s)). Qed.
Lemma lem4468368 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term298 A K k t s) = (term315 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468367 A K i k t s)). Qed.
Lemma lem4468369 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468370 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term299 A K k t s) = (term316 A K k t s).
Proof. exact (MK_COMB (@lem4468369 K) (@lem4468368 A K k t s)). Qed.
Lemma lem4468371 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term282 A K k t s) = (term316 A K k t s).
Proof. exact (TRANS (@lem4468343 A K k t s) (@lem4468370 A K k t s)). Qed.
Lemma lem4468372 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term165 A K k t s) = (term316 A K k t s).
Proof. exact (TRANS (@lem4468319 A K k t s) (@lem4468371 A K k t s)). Qed.
Lemma lem4468373 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term173 A K k t s) = (term317 A K k t s).
Proof. exact (MK_COMB (@lem4468207 A K k t s) (@lem4468372 A K k t s)). Qed.
Lemma lem4468375 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4468376 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term174 K P Q) = (term175 K P Q).
Proof. exact (@lem4468375 K P Q). Qed.
Lemma lem4468377 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term318 A K k t s) = (term319 A K k t s).
Proof. exact (@lem4468376 K (term233 A K k t s) (term315 A K k t s)). Qed.
Lemma lem4468378 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term320 A K k t s i) = (term232 A K k t s i).
Proof. exact (eq_refl (term320 A K k t s i)). Qed.
Lemma lem4468379 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term321 A K k t s) = (term233 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468378 A K k t s i)). Qed.
Lemma lem4468380 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468381 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term322 A K k t s) = (term234 A K k t s).
Proof. exact (MK_COMB (@lem4468380 K) (@lem4468379 A K k t s)). Qed.
Lemma lem4468382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468383 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term323 A K k t s) = (term235 A K k t s).
Proof. exact (MK_COMB (@lem4468382) (@lem4468381 A K k t s)). Qed.
Lemma lem4468384 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term324 A K k t s i) = (term314 A K i k t s).
Proof. exact (eq_refl (term324 A K k t s i)). Qed.
Lemma lem4468385 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term325 A K k t s) = (term315 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468384 A K i k t s)). Qed.
Lemma lem4468386 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468387 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term326 A K k t s) = (term316 A K k t s).
Proof. exact (MK_COMB (@lem4468386 K) (@lem4468385 A K k t s)). Qed.
Lemma lem4468388 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term318 A K k t s) = (term317 A K k t s).
Proof. exact (MK_COMB (@lem4468383 A K k t s) (@lem4468387 A K k t s)). Qed.
Lemma lem4468389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468390 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term327 A K k t s) = (term328 A K k t s).
Proof. exact (MK_COMB (@lem4468389) (@lem4468388 A K k t s)). Qed.
Lemma lem4468391 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term320 A K k t s i) = (term232 A K k t s i).
Proof. exact (eq_refl (term320 A K k t s i)). Qed.
Lemma lem4468392 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468393 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term329 A K k t s i) = (term330 A K k t s i).
Proof. exact (MK_COMB (@lem4468392) (@lem4468391 A K k t s i)). Qed.
Lemma lem4468394 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term324 A K k t s i) = (term314 A K i k t s).
Proof. exact (eq_refl (term324 A K k t s i)). Qed.
Lemma lem4468395 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term331 A K k t s i) = (term332 A K i k t s).
Proof. exact (MK_COMB (@lem4468393 A K k t s i) (@lem4468394 A K i k t s)). Qed.
Lemma lem4468396 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term333 A K k t s) = (term334 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468395 A K i k t s)). Qed.
Lemma lem4468397 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468398 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term319 A K k t s) = (term335 A K k t s).
Proof. exact (MK_COMB (@lem4468397 K) (@lem4468396 A K k t s)). Qed.
Lemma lem4468399 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term318 A K k t s) = (term319 A K k t s)) = ((term317 A K k t s) = (term335 A K k t s)).
Proof. exact (MK_COMB (@lem4468390 A K k t s) (@lem4468398 A K k t s)). Qed.
Lemma lem4468400 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term317 A K k t s) = (term335 A K k t s).
Proof. exact (EQ_MP (@lem4468399 A K k t s) (@lem4468377 A K k t s)). Qed.
Lemma lem4468402 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4468403 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term174 A P Q) = (term175 A P Q).
Proof. exact (@lem4468402 A P Q). Qed.
Lemma lem4468404 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term336 A K i k t s) = (term337 A K i k t s).
Proof. exact (@lem4468403 A (term231 A K k t s i) (term313 A K i k t s)). Qed.
Lemma lem4468405 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term338 A K k t s i x) = (term229 A K k t s i x).
Proof. exact (eq_refl (term338 A K k t s i x)). Qed.
Lemma lem4468406 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term339 A K k t s i) = (term231 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468405 A K k t s i x)). Qed.
Lemma lem4468407 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468408 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term340 A K k t s i) = (term232 A K k t s i).
Proof. exact (MK_COMB (@lem4468407 A) (@lem4468406 A K k t s i)). Qed.
Lemma lem4468409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468410 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term341 A K k t s i) = (term330 A K k t s i).
Proof. exact (MK_COMB (@lem4468409) (@lem4468408 A K k t s i)). Qed.
Lemma lem4468411 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term342 A K i k t s x) = (term311 A K i x k t s).
Proof. exact (eq_refl (term342 A K i k t s x)). Qed.
Lemma lem4468412 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term343 A K i k t s) = (term313 A K i k t s).
Proof. exact (fun_ext (fun x : A => @lem4468411 A K i x k t s)). Qed.
Lemma lem4468413 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468414 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term344 A K i k t s) = (term314 A K i k t s).
Proof. exact (MK_COMB (@lem4468413 A) (@lem4468412 A K i k t s)). Qed.
Lemma lem4468415 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term336 A K i k t s) = (term332 A K i k t s).
Proof. exact (MK_COMB (@lem4468410 A K k t s i) (@lem4468414 A K i k t s)). Qed.
Lemma lem4468416 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468417 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term345 A K i k t s) = (term346 A K i k t s).
Proof. exact (MK_COMB (@lem4468416) (@lem4468415 A K i k t s)). Qed.
Lemma lem4468418 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term338 A K k t s i x) = (term229 A K k t s i x).
Proof. exact (eq_refl (term338 A K k t s i x)). Qed.
Lemma lem4468419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468420 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term347 A K k t s i x) = (term348 A K k t s i x).
Proof. exact (MK_COMB (@lem4468419) (@lem4468418 A K k t s i x)). Qed.
Lemma lem4468421 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term342 A K i k t s x) = (term311 A K i x k t s).
Proof. exact (eq_refl (term342 A K i k t s x)). Qed.
Lemma lem4468422 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term349 A K i k t s x) = (term350 A K i x k t s).
Proof. exact (MK_COMB (@lem4468420 A K k t s i x) (@lem4468421 A K i x k t s)). Qed.
Lemma lem4468423 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term351 A K i k t s) = (term352 A K i k t s).
Proof. exact (fun_ext (fun x : A => @lem4468422 A K i x k t s)). Qed.
Lemma lem4468424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4468425 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term337 A K i k t s) = (term353 A K i k t s).
Proof. exact (MK_COMB (@lem4468424 A) (@lem4468423 A K i k t s)). Qed.
Lemma lem4468426 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : ((term336 A K i k t s) = (term337 A K i k t s)) = ((term332 A K i k t s) = (term353 A K i k t s)).
Proof. exact (MK_COMB (@lem4468417 A K i k t s) (@lem4468425 A K i k t s)). Qed.
Lemma lem4468427 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term332 A K i k t s) = (term353 A K i k t s).
Proof. exact (EQ_MP (@lem4468426 A K i k t s) (@lem4468404 A K i k t s)). Qed.
Lemma lem4468428 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term334 A K k t s) = (term354 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468427 A K i k t s)). Qed.
Lemma lem4468429 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4468430 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term335 A K k t s) = (term355 A K k t s).
Proof. exact (MK_COMB (@lem4468429 K) (@lem4468428 A K k t s)). Qed.
Lemma lem4468431 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term317 A K k t s) = (term355 A K k t s).
Proof. exact (TRANS (@lem4468400 A K k t s) (@lem4468430 A K k t s)). Qed.
Lemma lem4468433 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term173 A K k t s) = (term355 A K k t s).
Proof. exact (TRANS (@lem4468373 A K k t s) (@lem4468431 A K k t s)). Qed.
Lemma lem4468434 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term103 A K k t s) = (term355 A K k t s).
Proof. exact (TRANS (@lem4467492 A K k t s) (@lem4468433 A K k t s)). Qed.
Lemma lem4468435 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term103 A K k t s) : term355 A K k t s.
Proof. exact (EQ_MP (@lem4468434 A K k t s) (@lem4467282 A K k t s h1)). Qed.
Lemma lem4468436 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term353 A K i k t s) : term353 A K i k t s.
Proof. exact (h1). Qed.
Lemma lem4468437 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term350 A K i x k t s) : term350 A K i x k t s.
Proof. exact (h1). Qed.
Lemma lem4468452 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term106 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term106 A K t s i x)). Qed.
Lemma lem4468453 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term116 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468452 A K t s i x)). Qed.
Lemma lem4468454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468455 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term117 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4468454 A) (@lem4468453 A K t s i)). Qed.
Lemma lem4468470 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term106 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term106 A K s t i x)). Qed.
Lemma lem4468471 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term116 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468470 A K s t i x)). Qed.
Lemma lem4468472 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468473 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term117 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4468472 A) (@lem4468471 A K s t i)). Qed.
Lemma lem4468474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468475 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term146 A K s t i) = (term146 A K s t i).
Proof. exact (MK_COMB (@lem4468474) (@lem4468473 A K s t i)). Qed.
Lemma lem4468476 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term147 A K t s i) = (term147 A K t s i).
Proof. exact (MK_COMB (@lem4468475 A K s t i) (@lem4468455 A K t s i)). Qed.
Lemma lem4468483 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468484 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term152 A K k t s i) = (term152 A K k t s i).
Proof. exact (MK_COMB (@lem4468483 K k i) (@lem4468476 A K t s i)). Qed.
Lemma lem4468485 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term160 A K k t s) = (term160 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468484 A K k t s i)). Qed.
Lemma lem4468486 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468487 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term161 A K k t s).
Proof. exact (MK_COMB (@lem4468486 K) (@lem4468485 A K k t s)). Qed.
Lemma lem4468534 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term309 A K k t s i x) = (term309 A K k t s i x).
Proof. exact (eq_refl (term309 A K k t s i x)). Qed.
Lemma lem4468535 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term311 A K i x k t s) = (term311 A K i x k t s).
Proof. exact (MK_COMB (@lem4468534 A K k t s i x) (@lem4468487 A K k t s)). Qed.
Lemma lem4468574 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term202 A K k t s i x) = (term202 A K k t s i x).
Proof. exact (eq_refl (term202 A K k t s i x)). Qed.
Lemma lem4468589 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term106 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term106 A K t s i x)). Qed.
Lemma lem4468590 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term116 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468589 A K t s i x)). Qed.
Lemma lem4468591 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468592 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term117 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4468591 A) (@lem4468590 A K t s i)). Qed.
Lemma lem4468599 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468600 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term124 A K k t s i) = (term124 A K k t s i).
Proof. exact (MK_COMB (@lem4468599 K k i) (@lem4468592 A K t s i)). Qed.
Lemma lem4468601 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term132 A K k t s) = (term132 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468600 A K k t s i)). Qed.
Lemma lem4468602 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468603 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term133 A K k t s) = (term133 A K k t s).
Proof. exact (MK_COMB (@lem4468602 K) (@lem4468601 A K k t s)). Qed.
Lemma lem4468618 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term106 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term106 A K s t i x)). Qed.
Lemma lem4468619 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term116 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468618 A K s t i x)). Qed.
Lemma lem4468620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468621 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term117 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4468620 A) (@lem4468619 A K s t i)). Qed.
Lemma lem4468628 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468629 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term124 A K k s t i) = (term124 A K k s t i).
Proof. exact (MK_COMB (@lem4468628 K k i) (@lem4468621 A K s t i)). Qed.
Lemma lem4468630 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term132 A K k s t) = (term132 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4468629 A K k s t i)). Qed.
Lemma lem4468631 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468632 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term133 A K k s t) = (term133 A K k s t).
Proof. exact (MK_COMB (@lem4468631 K) (@lem4468630 A K k s t)). Qed.
Lemma lem4468633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term139 A K k s t) = (term139 A K k s t).
Proof. exact (MK_COMB (@lem4468633) (@lem4468632 A K k s t)). Qed.
Lemma lem4468635 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term140 A K k t s) = (term140 A K k t s).
Proof. exact (MK_COMB (@lem4468634 A K k s t) (@lem4468603 A K k t s)). Qed.
Lemma lem4468636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468637 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term167 A K k t s) = (term167 A K k t s).
Proof. exact (MK_COMB (@lem4468636) (@lem4468635 A K k t s)). Qed.
Lemma lem4468638 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term229 A K k t s i x) = (term229 A K k t s i x).
Proof. exact (MK_COMB (@lem4468637 A K k t s) (@lem4468574 A K k t s i x)). Qed.
Lemma lem4468639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4468640 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term348 A K k t s i x) = (term348 A K k t s i x).
Proof. exact (MK_COMB (@lem4468639) (@lem4468638 A K k t s i x)). Qed.
Lemma lem4468641 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term350 A K i x k t s) = (term350 A K i x k t s).
Proof. exact (MK_COMB (@lem4468640 A K k t s i x) (@lem4468535 A K i x k t s)). Qed.
Lemma lem4468642 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term350 A K i x k t s) : term350 A K i x k t s.
Proof. exact (EQ_MP (@lem4468641 A K i x k t s) (@lem4468437 A K i x k t s h1)). Qed.
Lemma lem4468643 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term229 A K k t s i x.
Proof. exact (h1). Qed.
Lemma lem4468644 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term311 A K i x k t s.
Proof. exact (h1). Qed.
Lemma lem4468645 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term202 A K k t s i x.
Proof. exact (proj2 (@lem4468643 A K k t s i x h1)). Qed.
Lemma lem4468646 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term140 A K k t s.
Proof. exact (proj1 (@lem4468643 A K k t s i x h1)). Qed.
Lemma lem4468647 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term187 A K t s i x.
Proof. exact (proj2 (@lem4468645 A K k t s i x h1)). Qed.
Lemma lem4468649 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term133 A K k t s.
Proof. exact (proj2 (@lem4468646 A K k t s i x h1)). Qed.
Lemma lem4468650 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term133 A K k s t.
Proof. exact (proj1 (@lem4468646 A K k t s i x h1)). Qed.
Lemma lem4468651 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : term105 A K s t i x.
Proof. exact (h1). Qed.
Lemma lem4468652 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : term105 A K t s i x.
Proof. exact (h1). Qed.
Lemma lem4468657 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term161 A K k t s.
Proof. exact (proj2 (@lem4468644 A K i x k t s h1)). Qed.
Lemma lem4468658 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term275 A K k t s i x.
Proof. exact (proj1 (@lem4468644 A K i x k t s h1)). Qed.
Lemma lem4468659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term241 A K k s t i x.
Proof. exact (h1). Qed.
Lemma lem4468660 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term241 A K k t s i x.
Proof. exact (h1). Qed.
Lemma lem4468661 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term105 A K s t i x.
Proof. exact (proj2 (@lem4468659 A K k s t i x h1)). Qed.
Lemma lem4468665 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term105 A K t s i x.
Proof. exact (proj2 (@lem4468660 A K k t s i x h1)). Qed.
Lemma lem4468674 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4468675 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (@lem4468674 A P Q). Qed.
Lemma lem4468676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term358 A K k s t i) = (term359 A K k s t i).
Proof. exact (@lem4468675 A (term360 K k i) (term116 A K s t i)). Qed.
Lemma lem4468677 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468678 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term362 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468677 A K s t i x)). Qed.
Lemma lem4468679 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468680 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term363 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4468679 A) (@lem4468678 A K s t i)). Qed.
Lemma lem4468681 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468682 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term358 A K k s t i) = (term124 A K k s t i).
Proof. exact (MK_COMB (@lem4468681 K k i) (@lem4468680 A K s t i)). Qed.
Lemma lem4468683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468684 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term364 A K k s t i) = (term365 A K k s t i).
Proof. exact (MK_COMB (@lem4468683) (@lem4468682 A K k s t i)). Qed.
Lemma lem4468685 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468686 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468687 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term366 A K k s t i x) = (term367 A K k s t i x).
Proof. exact (MK_COMB (@lem4468686 K k i) (@lem4468685 A K s t i x)). Qed.
Lemma lem4468688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term368 A K k s t i) = (term369 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4468687 A K k s t i x)). Qed.
Lemma lem4468689 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468690 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term359 A K k s t i) = (term370 A K k s t i).
Proof. exact (MK_COMB (@lem4468689 A) (@lem4468688 A K k s t i)). Qed.
Lemma lem4468691 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term358 A K k s t i) = (term359 A K k s t i)) = ((term124 A K k s t i) = (term370 A K k s t i)).
Proof. exact (MK_COMB (@lem4468684 A K k s t i) (@lem4468690 A K k s t i)). Qed.
Lemma lem4468692 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term124 A K k s t i) = (term370 A K k s t i).
Proof. exact (EQ_MP (@lem4468691 A K k s t i) (@lem4468676 A K k s t i)). Qed.
Lemma lem4468693 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term132 A K k s t) = (term371 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4468692 A K k s t i)). Qed.
Lemma lem4468694 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468695 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term133 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4468694 K) (@lem4468693 A K k s t)). Qed.
Lemma lem4468708 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term367 A K k s t i x) = (term367 A K k s t i x).
Proof. exact (eq_refl (term367 A K k s t i x)). Qed.
Lemma lem4468709 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term369 A K k s t i) = (term369 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4468708 A K k s t i x)). Qed.
Lemma lem4468710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468711 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term370 A K k s t i) = (term370 A K k s t i).
Proof. exact (MK_COMB (@lem4468710 A) (@lem4468709 A K k s t i)). Qed.
Lemma lem4468712 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term371 A K k s t) = (term371 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4468711 A K k s t i)). Qed.
Lemma lem4468713 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468714 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term372 A K k s t) = (term372 A K k s t).
Proof. exact (MK_COMB (@lem4468713 K) (@lem4468712 A K k s t)). Qed.
Lemma lem4468715 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term133 A K k s t) = (term372 A K k s t).
Proof. exact (TRANS (@lem4468695 A K k s t) (@lem4468714 A K k s t)). Qed.
Lemma lem4468716 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term372 A K k s t.
Proof. exact (EQ_MP (@lem4468715 A K k s t) (@lem4468650 A K k t s i x h1)). Qed.
Lemma lem4468818 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4468819 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (@lem4468818 A P Q). Qed.
Lemma lem4468820 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term358 A K k t s i) = (term359 A K k t s i).
Proof. exact (@lem4468819 A (term360 K k i) (term116 A K t s i)). Qed.
Lemma lem4468821 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468822 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term362 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468821 A K t s i x)). Qed.
Lemma lem4468823 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468824 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term363 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4468823 A) (@lem4468822 A K t s i)). Qed.
Lemma lem4468825 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468826 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term358 A K k t s i) = (term124 A K k t s i).
Proof. exact (MK_COMB (@lem4468825 K k i) (@lem4468824 A K t s i)). Qed.
Lemma lem4468827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468828 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term364 A K k t s i) = (term365 A K k t s i).
Proof. exact (MK_COMB (@lem4468827) (@lem4468826 A K k t s i)). Qed.
Lemma lem4468829 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468830 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468831 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term366 A K k t s i x) = (term367 A K k t s i x).
Proof. exact (MK_COMB (@lem4468830 K k i) (@lem4468829 A K t s i x)). Qed.
Lemma lem4468832 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term368 A K k t s i) = (term369 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468831 A K k t s i x)). Qed.
Lemma lem4468833 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468834 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term359 A K k t s i) = (term370 A K k t s i).
Proof. exact (MK_COMB (@lem4468833 A) (@lem4468832 A K k t s i)). Qed.
Lemma lem4468835 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term358 A K k t s i) = (term359 A K k t s i)) = ((term124 A K k t s i) = (term370 A K k t s i)).
Proof. exact (MK_COMB (@lem4468828 A K k t s i) (@lem4468834 A K k t s i)). Qed.
Lemma lem4468836 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term124 A K k t s i) = (term370 A K k t s i).
Proof. exact (EQ_MP (@lem4468835 A K k t s i) (@lem4468820 A K k t s i)). Qed.
Lemma lem4468837 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term132 A K k t s) = (term371 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468836 A K k t s i)). Qed.
Lemma lem4468838 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468839 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term133 A K k t s) = (term372 A K k t s).
Proof. exact (MK_COMB (@lem4468838 K) (@lem4468837 A K k t s)). Qed.
Lemma lem4468852 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term367 A K k t s i x) = (term367 A K k t s i x).
Proof. exact (eq_refl (term367 A K k t s i x)). Qed.
Lemma lem4468853 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term369 A K k t s i) = (term369 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468852 A K k t s i x)). Qed.
Lemma lem4468854 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468855 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term370 A K k t s i) = (term370 A K k t s i).
Proof. exact (MK_COMB (@lem4468854 A) (@lem4468853 A K k t s i)). Qed.
Lemma lem4468856 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term371 A K k t s) = (term371 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468855 A K k t s i)). Qed.
Lemma lem4468857 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468858 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term372 A K k t s) = (term372 A K k t s).
Proof. exact (MK_COMB (@lem4468857 K) (@lem4468856 A K k t s)). Qed.
Lemma lem4468859 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term133 A K k t s) = (term372 A K k t s).
Proof. exact (TRANS (@lem4468839 A K k t s) (@lem4468858 A K k t s)). Qed.
Lemma lem4468860 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term372 A K k t s.
Proof. exact (EQ_MP (@lem4468859 A K k t s) (@lem4468649 A K k t s i x h1)). Qed.
Lemma lem4468870 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4468871 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (@lem4468870 A P Q). Qed.
Lemma lem4468872 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term375 A K t s i) = (term376 A K t s i).
Proof. exact (@lem4468871 A (term116 A K s t i) (term116 A K t s i)). Qed.
Lemma lem4468873 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468874 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term362 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468873 A K s t i x)). Qed.
Lemma lem4468875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468876 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term363 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4468875 A) (@lem4468874 A K s t i)). Qed.
Lemma lem4468877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468878 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term377 A K s t i) = (term146 A K s t i).
Proof. exact (MK_COMB (@lem4468877) (@lem4468876 A K s t i)). Qed.
Lemma lem4468879 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468880 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term362 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468879 A K t s i x)). Qed.
Lemma lem4468881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468882 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term363 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4468881 A) (@lem4468880 A K t s i)). Qed.
Lemma lem4468883 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term375 A K t s i) = (term147 A K t s i).
Proof. exact (MK_COMB (@lem4468878 A K s t i) (@lem4468882 A K t s i)). Qed.
Lemma lem4468884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468885 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term378 A K t s i) = (term379 A K t s i).
Proof. exact (MK_COMB (@lem4468884) (@lem4468883 A K t s i)). Qed.
Lemma lem4468886 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468888 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term380 A K s t i x) = (term381 A K s t i x).
Proof. exact (MK_COMB (@lem4468887) (@lem4468886 A K s t i x)). Qed.
Lemma lem4468889 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468890 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term382 A K t s i x) = (term383 A K t s i x).
Proof. exact (MK_COMB (@lem4468888 A K s t i x) (@lem4468889 A K t s i x)). Qed.
Lemma lem4468891 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term384 A K t s i) = (term385 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468890 A K t s i x)). Qed.
Lemma lem4468892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468893 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term376 A K t s i) = (term386 A K t s i).
Proof. exact (MK_COMB (@lem4468892 A) (@lem4468891 A K t s i)). Qed.
Lemma lem4468894 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : ((term375 A K t s i) = (term376 A K t s i)) = ((term147 A K t s i) = (term386 A K t s i)).
Proof. exact (MK_COMB (@lem4468885 A K t s i) (@lem4468893 A K t s i)). Qed.
Lemma lem4468895 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term147 A K t s i) = (term386 A K t s i).
Proof. exact (EQ_MP (@lem4468894 A K t s i) (@lem4468872 A K t s i)). Qed.
Lemma lem4468896 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468897 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term152 A K k t s i) = (term387 A K k t s i).
Proof. exact (MK_COMB (@lem4468896 K k i) (@lem4468895 A K t s i)). Qed.
Lemma lem4468899 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4468900 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (@lem4468899 A P Q). Qed.
Lemma lem4468901 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term388 A K k t s i) = (term389 A K k t s i).
Proof. exact (@lem4468900 A (term360 K k i) (term385 A K t s i)). Qed.
Lemma lem4468902 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term390 A K t s i x) = (term383 A K t s i x).
Proof. exact (eq_refl (term390 A K t s i x)). Qed.
Lemma lem4468903 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term391 A K t s i) = (term385 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468902 A K t s i x)). Qed.
Lemma lem4468904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468905 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term392 A K t s i) = (term386 A K t s i).
Proof. exact (MK_COMB (@lem4468904 A) (@lem4468903 A K t s i)). Qed.
Lemma lem4468906 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468907 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term388 A K k t s i) = (term387 A K k t s i).
Proof. exact (MK_COMB (@lem4468906 K k i) (@lem4468905 A K t s i)). Qed.
Lemma lem4468908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468909 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term393 A K k t s i) = (term394 A K k t s i).
Proof. exact (MK_COMB (@lem4468908) (@lem4468907 A K k t s i)). Qed.
Lemma lem4468910 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term390 A K t s i x) = (term383 A K t s i x).
Proof. exact (eq_refl (term390 A K t s i x)). Qed.
Lemma lem4468911 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468912 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term395 A K k t s i x) = (term396 A K k t s i x).
Proof. exact (MK_COMB (@lem4468911 K k i) (@lem4468910 A K t s i x)). Qed.
Lemma lem4468913 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term397 A K k t s i) = (term398 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468912 A K k t s i x)). Qed.
Lemma lem4468914 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468915 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term389 A K k t s i) = (term399 A K k t s i).
Proof. exact (MK_COMB (@lem4468914 A) (@lem4468913 A K k t s i)). Qed.
Lemma lem4468916 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term388 A K k t s i) = (term389 A K k t s i)) = ((term387 A K k t s i) = (term399 A K k t s i)).
Proof. exact (MK_COMB (@lem4468909 A K k t s i) (@lem4468915 A K k t s i)). Qed.
Lemma lem4468917 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term387 A K k t s i) = (term399 A K k t s i).
Proof. exact (EQ_MP (@lem4468916 A K k t s i) (@lem4468901 A K k t s i)). Qed.
Lemma lem4468918 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term152 A K k t s i) = (term399 A K k t s i).
Proof. exact (TRANS (@lem4468897 A K k t s i) (@lem4468917 A K k t s i)). Qed.
Lemma lem4468919 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term160 A K k t s) = (term400 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468918 A K k t s i)). Qed.
Lemma lem4468920 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468921 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term401 A K k t s).
Proof. exact (MK_COMB (@lem4468920 K) (@lem4468919 A K k t s)). Qed.
Lemma lem4468950 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term396 A K k t s i x) = (term402 A K k t s i x).
Proof. exact (@lem19490 (term106 A K s t i x) (term360 K k i) (term106 A K t s i x)). Qed.
Lemma lem4468951 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term398 A K k t s i) = (term403 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4468950 A K k t s i x)). Qed.
Lemma lem4468952 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468953 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term399 A K k t s i) = (term404 A K k t s i).
Proof. exact (MK_COMB (@lem4468952 A) (@lem4468951 A K k t s i)). Qed.
Lemma lem4468954 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term400 A K k t s) = (term405 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4468953 A K k t s i)). Qed.
Lemma lem4468955 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4468956 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term401 A K k t s) = (term406 A K k t s).
Proof. exact (MK_COMB (@lem4468955 K) (@lem4468954 A K k t s)). Qed.
Lemma lem4468957 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term406 A K k t s).
Proof. exact (TRANS (@lem4468921 A K k t s) (@lem4468956 A K k t s)). Qed.
Lemma lem4468958 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term406 A K k t s.
Proof. exact (EQ_MP (@lem4468957 A K k t s) (@lem4468657 A K i x k t s h1)). Qed.
Lemma lem4468972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem4468973 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term373 A P Q) = (term374 A P Q).
Proof. exact (@lem4468972 A P Q). Qed.
Lemma lem4468974 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term375 A K t s i) = (term376 A K t s i).
Proof. exact (@lem4468973 A (term116 A K s t i) (term116 A K t s i)). Qed.
Lemma lem4468975 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468976 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term362 A K s t i) = (term116 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4468975 A K s t i x)). Qed.
Lemma lem4468977 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468978 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term363 A K s t i) = (term117 A K s t i).
Proof. exact (MK_COMB (@lem4468977 A) (@lem4468976 A K s t i)). Qed.
Lemma lem4468979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468980 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term377 A K s t i) = (term146 A K s t i).
Proof. exact (MK_COMB (@lem4468979) (@lem4468978 A K s t i)). Qed.
Lemma lem4468981 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468982 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term362 A K t s i) = (term116 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468981 A K t s i x)). Qed.
Lemma lem4468983 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468984 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term363 A K t s i) = (term117 A K t s i).
Proof. exact (MK_COMB (@lem4468983 A) (@lem4468982 A K t s i)). Qed.
Lemma lem4468985 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term375 A K t s i) = (term147 A K t s i).
Proof. exact (MK_COMB (@lem4468980 A K s t i) (@lem4468984 A K t s i)). Qed.
Lemma lem4468986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4468987 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term378 A K t s i) = (term379 A K t s i).
Proof. exact (MK_COMB (@lem4468986) (@lem4468985 A K t s i)). Qed.
Lemma lem4468988 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term361 A K s t i x) = (term106 A K s t i x).
Proof. exact (eq_refl (term361 A K s t i x)). Qed.
Lemma lem4468989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4468990 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term380 A K s t i x) = (term381 A K s t i x).
Proof. exact (MK_COMB (@lem4468989) (@lem4468988 A K s t i x)). Qed.
Lemma lem4468991 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term361 A K t s i x) = (term106 A K t s i x).
Proof. exact (eq_refl (term361 A K t s i x)). Qed.
Lemma lem4468992 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term382 A K t s i x) = (term383 A K t s i x).
Proof. exact (MK_COMB (@lem4468990 A K s t i x) (@lem4468991 A K t s i x)). Qed.
Lemma lem4468993 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term384 A K t s i) = (term385 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4468992 A K t s i x)). Qed.
Lemma lem4468994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4468995 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term376 A K t s i) = (term386 A K t s i).
Proof. exact (MK_COMB (@lem4468994 A) (@lem4468993 A K t s i)). Qed.
Lemma lem4468996 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : ((term375 A K t s i) = (term376 A K t s i)) = ((term147 A K t s i) = (term386 A K t s i)).
Proof. exact (MK_COMB (@lem4468987 A K t s i) (@lem4468995 A K t s i)). Qed.
Lemma lem4468997 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term147 A K t s i) = (term386 A K t s i).
Proof. exact (EQ_MP (@lem4468996 A K t s i) (@lem4468974 A K t s i)). Qed.
Lemma lem4468998 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4468999 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term152 A K k t s i) = (term387 A K k t s i).
Proof. exact (MK_COMB (@lem4468998 K k i) (@lem4468997 A K t s i)). Qed.
Lemma lem4469001 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4469002 {A : Type'} (P : Prop) (Q : A -> Prop) : (term356 A P Q) = (term357 A P Q).
Proof. exact (@lem4469001 A P Q). Qed.
Lemma lem4469003 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term388 A K k t s i) = (term389 A K k t s i).
Proof. exact (@lem4469002 A (term360 K k i) (term385 A K t s i)). Qed.
Lemma lem4469004 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term390 A K t s i x) = (term383 A K t s i x).
Proof. exact (eq_refl (term390 A K t s i x)). Qed.
Lemma lem4469005 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term391 A K t s i) = (term385 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4469004 A K t s i x)). Qed.
Lemma lem4469006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4469007 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term392 A K t s i) = (term386 A K t s i).
Proof. exact (MK_COMB (@lem4469006 A) (@lem4469005 A K t s i)). Qed.
Lemma lem4469008 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4469009 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term388 A K k t s i) = (term387 A K k t s i).
Proof. exact (MK_COMB (@lem4469008 K k i) (@lem4469007 A K t s i)). Qed.
Lemma lem4469010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4469011 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term393 A K k t s i) = (term394 A K k t s i).
Proof. exact (MK_COMB (@lem4469010) (@lem4469009 A K k t s i)). Qed.
Lemma lem4469012 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term390 A K t s i x) = (term383 A K t s i x).
Proof. exact (eq_refl (term390 A K t s i x)). Qed.
Lemma lem4469013 {K : Type'} (k : K -> Prop) (i : K) : (term122 K k i) = (term122 K k i).
Proof. exact (eq_refl (term122 K k i)). Qed.
Lemma lem4469014 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term395 A K k t s i x) = (term396 A K k t s i x).
Proof. exact (MK_COMB (@lem4469013 K k i) (@lem4469012 A K t s i x)). Qed.
Lemma lem4469015 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term397 A K k t s i) = (term398 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4469014 A K k t s i x)). Qed.
Lemma lem4469016 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4469017 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term389 A K k t s i) = (term399 A K k t s i).
Proof. exact (MK_COMB (@lem4469016 A) (@lem4469015 A K k t s i)). Qed.
Lemma lem4469018 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term388 A K k t s i) = (term389 A K k t s i)) = ((term387 A K k t s i) = (term399 A K k t s i)).
Proof. exact (MK_COMB (@lem4469011 A K k t s i) (@lem4469017 A K k t s i)). Qed.
Lemma lem4469019 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term387 A K k t s i) = (term399 A K k t s i).
Proof. exact (EQ_MP (@lem4469018 A K k t s i) (@lem4469003 A K k t s i)). Qed.
Lemma lem4469020 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term152 A K k t s i) = (term399 A K k t s i).
Proof. exact (TRANS (@lem4468999 A K k t s i) (@lem4469019 A K k t s i)). Qed.
Lemma lem4469021 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term160 A K k t s) = (term400 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4469020 A K k t s i)). Qed.
Lemma lem4469022 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4469023 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term401 A K k t s).
Proof. exact (MK_COMB (@lem4469022 K) (@lem4469021 A K k t s)). Qed.
Lemma lem4469052 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term396 A K k t s i x) = (term402 A K k t s i x).
Proof. exact (@lem19490 (term106 A K s t i x) (term360 K k i) (term106 A K t s i x)). Qed.
Lemma lem4469053 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term398 A K k t s i) = (term403 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4469052 A K k t s i x)). Qed.
Lemma lem4469054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4469055 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term399 A K k t s i) = (term404 A K k t s i).
Proof. exact (MK_COMB (@lem4469054 A) (@lem4469053 A K k t s i)). Qed.
Lemma lem4469056 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term400 A K k t s) = (term405 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4469055 A K k t s i)). Qed.
Lemma lem4469057 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4469058 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term401 A K k t s) = (term406 A K k t s).
Proof. exact (MK_COMB (@lem4469057 K) (@lem4469056 A K k t s)). Qed.
Lemma lem4469059 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term161 A K k t s) = (term406 A K k t s).
Proof. exact (TRANS (@lem4469023 A K k t s) (@lem4469058 A K k t s)). Qed.
Lemma lem4469060 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term406 A K k t s.
Proof. exact (EQ_MP (@lem4469059 A K k t s) (@lem4468657 A K i x k t s h1)). Qed.
Lemma lem4469073 {A K : Type'} (_51680 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term407 A K k s t _51680.
Proof. exact (@lem4468716 A K k t s i x h1 _51680). Qed.
Lemma lem4469074 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51680 : K) : (term407 A K k s t _51680) = (term370 A K k s t _51680).
Proof. exact (eq_refl (term407 A K k s t _51680)). Qed.
Lemma lem4469075 {A K : Type'} (_51680 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term370 A K k s t _51680.
Proof. exact (EQ_MP (@lem4469074 A K k s t _51680) (@lem4469073 A K _51680 k t s i x h1)). Qed.
Lemma lem4469076 {A K : Type'} (_51680 : K) (_51681 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term408 A K k s t _51680 _51681.
Proof. exact (@lem4469075 A K _51680 k t s i x h1 _51681). Qed.
Lemma lem4469077 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51680 : K) (_51681 : A) : (term408 A K k s t _51680 _51681) = (term367 A K k s t _51680 _51681).
Proof. exact (eq_refl (term408 A K k s t _51680 _51681)). Qed.
Lemma lem4469091 {A K : Type'} (_51686 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term407 A K k t s _51686.
Proof. exact (@lem4468860 A K k t s i x h1 _51686). Qed.
Lemma lem4469092 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51686 : K) : (term407 A K k t s _51686) = (term370 A K k t s _51686).
Proof. exact (eq_refl (term407 A K k t s _51686)). Qed.
Lemma lem4469093 {A K : Type'} (_51686 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term370 A K k t s _51686.
Proof. exact (EQ_MP (@lem4469092 A K k t s _51686) (@lem4469091 A K _51686 k t s i x h1)). Qed.
Lemma lem4469094 {A K : Type'} (_51686 : K) (_51687 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term408 A K k t s _51686 _51687.
Proof. exact (@lem4469093 A K _51686 k t s i x h1 _51687). Qed.
Lemma lem4469095 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51686 : K) (_51687 : A) : (term408 A K k t s _51686 _51687) = (term367 A K k t s _51686 _51687).
Proof. exact (eq_refl (term408 A K k t s _51686 _51687)). Qed.
Lemma lem4469097 {A K : Type'} (_51688 : K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term409 A K k t s _51688.
Proof. exact (@lem4468958 A K i x k t s h1 _51688). Qed.
Lemma lem4469098 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51688 : K) : (term409 A K k t s _51688) = (term404 A K k t s _51688).
Proof. exact (eq_refl (term409 A K k t s _51688)). Qed.
Lemma lem4469099 {A K : Type'} (_51688 : K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term404 A K k t s _51688.
Proof. exact (EQ_MP (@lem4469098 A K k t s _51688) (@lem4469097 A K _51688 i x k t s h1)). Qed.
Lemma lem4469100 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term410 A K k t s _51688 _51689.
Proof. exact (@lem4469099 A K _51688 i x k t s h1 _51689). Qed.
Lemma lem4469101 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term410 A K k t s _51688 _51689) = (term402 A K k t s _51688 _51689).
Proof. exact (eq_refl (term410 A K k t s _51688 _51689)). Qed.
Lemma lem4469102 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term402 A K k t s _51688 _51689.
Proof. exact (EQ_MP (@lem4469101 A K k t s _51688 _51689) (@lem4469100 A K _51688 _51689 i x k t s h1)). Qed.
Lemma lem4469103 {A K : Type'} (_51690 : K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term409 A K k t s _51690.
Proof. exact (@lem4469060 A K i x k t s h1 _51690). Qed.
Lemma lem4469104 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51690 : K) : (term409 A K k t s _51690) = (term404 A K k t s _51690).
Proof. exact (eq_refl (term409 A K k t s _51690)). Qed.
Lemma lem4469105 {A K : Type'} (_51690 : K) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term404 A K k t s _51690.
Proof. exact (EQ_MP (@lem4469104 A K k t s _51690) (@lem4469103 A K _51690 i x k t s h1)). Qed.
Lemma lem4469106 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term410 A K k t s _51690 _51691.
Proof. exact (@lem4469105 A K _51690 i x k t s h1 _51691). Qed.
Lemma lem4469107 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51690 : K) (_51691 : A) : (term410 A K k t s _51690 _51691) = (term402 A K k t s _51690 _51691).
Proof. exact (eq_refl (term410 A K k t s _51690 _51691)). Qed.
Lemma lem4469108 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term402 A K k t s _51690 _51691.
Proof. exact (EQ_MP (@lem4469107 A K k t s _51690 _51691) (@lem4469106 A K _51690 _51691 i x k t s h1)). Qed.
Lemma lem4469124 {A K : Type'} (_51680 : K) (_51681 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term367 A K k s t _51680 _51681.
Proof. exact (EQ_MP (@lem4469077 A K k s t _51680 _51681) (@lem4469076 A K _51680 _51681 k t s i x h1)). Qed.
Lemma lem4469138 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : term411 A K t i x.
Proof. exact (proj2 (@lem4468651 A K s t i x h1)). Qed.
Lemma lem4469160 {A K : Type'} (_51686 : K) (_51687 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term367 A K k t s _51686 _51687.
Proof. exact (EQ_MP (@lem4469095 A K k t s _51686 _51687) (@lem4469094 A K _51686 _51687 k t s i x h1)). Qed.
Lemma lem4469164 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : term411 A K s i x.
Proof. exact (proj2 (@lem4468652 A K t s i x h1)). Qed.
Lemma lem4469170 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term411 A K t i x.
Proof. exact (proj2 (@lem4468661 A K k s t i x h1)). Qed.
Lemma lem4469180 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term367 A K k s t _51688 _51689.
Proof. exact (proj1 (@lem4469102 A K _51688 _51689 i x k t s h1)). Qed.
Lemma lem4469196 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term411 A K s i x.
Proof. exact (proj2 (@lem4468665 A K k t s i x h1)). Qed.
Lemma lem4469216 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term367 A K k t s _51690 _51691.
Proof. exact (proj2 (@lem4469108 A K _51690 _51691 i x k t s h1)). Qed.
Lemma lem4469218 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : k i.
Proof. exact (proj1 (@lem4468645 A K k t s i x h1)). Qed.
Lemma lem4469219 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term412 K k i.
Proof. exact (fun h0 : term360 K k i => @lem4469218 A K k t s i x h1). Qed.
Lemma lem4469221 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469222 {K : Type'} (k : K -> Prop) (i : K) : (term412 K k i) = (k i).
Proof. exact (@lem4469221 (k i)). Qed.
Lemma lem4469223 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : k i.
Proof. exact (EQ_MP (@lem4469222 K k i) (@lem4469219 A K k t s i x h1)). Qed.
Lemma lem4469225 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : s i x.
Proof. exact (proj1 (@lem4468651 A K s t i x h1)). Qed.
Lemma lem4469226 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : term414 A K s i x.
Proof. exact (fun h0 : term411 A K s i x => @lem4469225 A K s t i x h1). Qed.
Lemma lem4469228 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469229 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term414 A K s i x) = (s i x).
Proof. exact (@lem4469228 (s i x)). Qed.
Lemma lem4469230 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : s i x.
Proof. exact (EQ_MP (@lem4469229 A K s i x) (@lem4469226 A K s t i x h1)). Qed.
Lemma lem4469246 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4469247 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term106 A K s t _51680 _51681) = (term415 A K t s _51680 _51681).
Proof. exact (@lem4469246 (t _51680 _51681) (term411 A K s _51680 _51681)). Qed.
Lemma lem4469253 {K : Type'} (k : K -> Prop) (_51680 : K) : (term122 K k _51680) = (term122 K k _51680).
Proof. exact (eq_refl (term122 K k _51680)). Qed.
Lemma lem4469254 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term367 A K k s t _51680 _51681) = (term416 A K k t s _51680 _51681).
Proof. exact (MK_COMB (@lem4469253 K k _51680) (@lem4469247 A K t s _51680 _51681)). Qed.
Lemma lem4469258 (q : Prop) (p : Prop) (r : Prop) : (term417 p q r) = (term417 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4469259 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term416 A K k t s _51680 _51681) = (term418 A K t k s _51680 _51681).
Proof. exact (@lem4469258 (t _51680 _51681) (term360 K k _51680) (term411 A K s _51680 _51681)). Qed.
Lemma lem4469275 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term367 A K k s t _51680 _51681) = (term418 A K t k s _51680 _51681).
Proof. exact (TRANS (@lem4469254 A K k t s _51680 _51681) (@lem4469259 A K t k s _51680 _51681)). Qed.
Lemma lem4469276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4469277 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term419 A K k s t _51680 _51681) = (term420 A K t k s _51680 _51681).
Proof. exact (MK_COMB (@lem4469276) (@lem4469275 A K t k s _51680 _51681)). Qed.
Lemma lem4469293 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term418 A K t k s _51680 _51681) = (term418 A K t k s _51680 _51681).
Proof. exact (eq_refl (term418 A K t k s _51680 _51681)). Qed.
Lemma lem4469294 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : ((term367 A K k s t _51680 _51681) = (term418 A K t k s _51680 _51681)) = ((term418 A K t k s _51680 _51681) = (term418 A K t k s _51680 _51681)).
Proof. exact (MK_COMB (@lem4469277 A K t k s _51680 _51681) (@lem4469293 A K t k s _51680 _51681)). Qed.
Lemma lem4469296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4469297 (x : Prop) : (x = x) = True.
Proof. exact (@lem4469296 Prop x). Qed.
Lemma lem4469298 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : ((term418 A K t k s _51680 _51681) = (term418 A K t k s _51680 _51681)) = True.
Proof. exact (@lem4469297 (term418 A K t k s _51680 _51681)). Qed.
Lemma lem4469299 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : ((term367 A K k s t _51680 _51681) = (term418 A K t k s _51680 _51681)) = True.
Proof. exact (TRANS (@lem4469294 A K t k s _51680 _51681) (@lem4469298 A K t k s _51680 _51681)). Qed.
Lemma lem4469300 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : True = ((term367 A K k s t _51680 _51681) = (term418 A K t k s _51680 _51681)).
Proof. exact (SYM (@lem4469299 A K t k s _51680 _51681)). Qed.
Lemma lem4469301 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term367 A K k s t _51680 _51681) = (term418 A K t k s _51680 _51681).
Proof. exact (EQ_MP (@lem4469300 A K t k s _51680 _51681) (@lem0)). Qed.
Lemma lem4469302 {A K : Type'} (_51680 : K) (_51681 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term418 A K t k s _51680 _51681.
Proof. exact (EQ_MP (@lem4469301 A K t k s _51680 _51681) (@lem4469124 A K _51680 _51681 k t s i x h1)). Qed.
Lemma lem4469304 (b : Prop) (a : Prop) : (a \/ b) = (term421 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4469305 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51680 : K) (_51681 : A) : (term418 A K t k s _51680 _51681) = (term422 A K k s t _51680 _51681).
Proof. exact (@lem4469304 (term423 A K k s _51680 _51681) (t _51680 _51681)). Qed.
Lemma lem4469307 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4469308 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term426 A K k s _51680 _51681) = (term427 A K k s _51680 _51681).
Proof. exact (@lem4469307 (term360 K k _51680) (term411 A K s _51680 _51681)). Qed.
Lemma lem4469310 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469311 {K : Type'} (k : K -> Prop) (_51680 : K) : (term428 K k _51680) = (k _51680).
Proof. exact (@lem4469310 (k _51680)). Qed.
Lemma lem4469312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4469313 {K : Type'} (k : K -> Prop) (_51680 : K) : (term429 K k _51680) = (term118 K k _51680).
Proof. exact (MK_COMB (@lem4469312) (@lem4469311 K k _51680)). Qed.
Lemma lem4469315 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469316 {A K : Type'} (s : type1470 A K) (_51680 : K) (_51681 : A) : (term430 A K s _51680 _51681) = (s _51680 _51681).
Proof. exact (@lem4469315 (s _51680 _51681)). Qed.
Lemma lem4469317 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term427 A K k s _51680 _51681) = (term431 A K k s _51680 _51681).
Proof. exact (MK_COMB (@lem4469313 K k _51680) (@lem4469316 A K s _51680 _51681)). Qed.
Lemma lem4469318 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term426 A K k s _51680 _51681) = (term431 A K k s _51680 _51681).
Proof. exact (TRANS (@lem4469308 A K k s _51680 _51681) (@lem4469317 A K k s _51680 _51681)). Qed.
Lemma lem4469319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4469320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51680 : K) (_51681 : A) : (term432 A K k s _51680 _51681) = (term433 A K k s _51680 _51681).
Proof. exact (MK_COMB (@lem4469319) (@lem4469318 A K k s _51680 _51681)). Qed.
Lemma lem4469321 {A K : Type'} (t : type1470 A K) (_51680 : K) (_51681 : A) : (t _51680 _51681) = (t _51680 _51681).
Proof. exact (eq_refl (t _51680 _51681)). Qed.
Lemma lem4469322 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51680 : K) (_51681 : A) : (term422 A K k s t _51680 _51681) = (term434 A K k s t _51680 _51681).
Proof. exact (MK_COMB (@lem4469320 A K k s _51680 _51681) (@lem4469321 A K t _51680 _51681)). Qed.
Lemma lem4469323 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51680 : K) (_51681 : A) : (term418 A K t k s _51680 _51681) = (term434 A K k s t _51680 _51681).
Proof. exact (TRANS (@lem4469305 A K k s t _51680 _51681) (@lem4469322 A K k s t _51680 _51681)). Qed.
Lemma lem4469325 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : term431 A K k s i x.
Proof. exact (conj (@lem4469223 A K k t s i x h1) (@lem4469230 A K s t i x h2)). Qed.
Lemma lem4469327 {A K : Type'} (_51680 : K) (_51681 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k s t _51680 _51681.
Proof. exact (EQ_MP (@lem4469323 A K k s t _51680 _51681) (@lem4469302 A K _51680 _51681 k t s i x h1)). Qed.
Lemma lem4469328 {A K : Type'} (_51680 : K) (_51681 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k s t _51680 _51681.
Proof. exact (@lem4469327 A K _51680 _51681 k t s i x h1). Qed.
Lemma lem4469329 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k s t i x.
Proof. exact (@lem4469328 A K i x k t s i x h1). Qed.
Lemma lem4469332 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : t i x.
Proof. exact (@lem4469329 A K k t s i x h1 (@lem4469325 A K k s t i x h1 h2)). Qed.
Lemma lem4469333 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : term414 A K t i x.
Proof. exact (fun h0 : term411 A K t i x => @lem4469332 A K k s t i x h1 h2). Qed.
Lemma lem4469335 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469336 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term414 A K t i x) = (t i x).
Proof. exact (@lem4469335 (t i x)). Qed.
Lemma lem4469337 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : t i x.
Proof. exact (EQ_MP (@lem4469336 A K t i x) (@lem4469333 A K k s t i x h1 h2)). Qed.
Lemma lem4469340 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4469342 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term411 A K t i x) = (term435 A K t i x).
Proof. exact (@lem4469340 (t i x)). Qed.
Lemma lem4469345 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term105 A K s t i x) : term435 A K t i x.
Proof. exact (EQ_MP (@lem4469342 A K t i x) (@lem4469138 A K s t i x h1)). Qed.
Lemma lem4469348 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : False.
Proof. exact (@lem4469345 A K s t i x h2 (@lem4469337 A K k s t i x h1 h2)). Qed.
Lemma lem4469349 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : term436.
Proof. exact (fun h0 : ~ False => @lem4469348 A K k s t i x h1 h2). Qed.
Lemma lem4469351 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469352 : term436 = False.
Proof. exact (@lem4469351 False). Qed.
Lemma lem4469353 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K s t i x) : False.
Proof. exact (EQ_MP (@lem4469352) (@lem4469349 A K k s t i x h1 h2)). Qed.
Lemma lem4469355 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : k i.
Proof. exact (proj1 (@lem4468645 A K k t s i x h1)). Qed.
Lemma lem4469356 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term412 K k i.
Proof. exact (fun h0 : term360 K k i => @lem4469355 A K k t s i x h1). Qed.
Lemma lem4469358 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469359 {K : Type'} (k : K -> Prop) (i : K) : (term412 K k i) = (k i).
Proof. exact (@lem4469358 (k i)). Qed.
Lemma lem4469360 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : k i.
Proof. exact (EQ_MP (@lem4469359 K k i) (@lem4469356 A K k t s i x h1)). Qed.
Lemma lem4469362 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : t i x.
Proof. exact (proj1 (@lem4468652 A K t s i x h1)). Qed.
Lemma lem4469363 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : term414 A K t i x.
Proof. exact (fun h0 : term411 A K t i x => @lem4469362 A K t s i x h1). Qed.
Lemma lem4469365 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469366 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term414 A K t i x) = (t i x).
Proof. exact (@lem4469365 (t i x)). Qed.
Lemma lem4469367 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : t i x.
Proof. exact (EQ_MP (@lem4469366 A K t i x) (@lem4469363 A K t s i x h1)). Qed.
Lemma lem4469383 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4469384 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term106 A K t s _51686 _51687) = (term415 A K s t _51686 _51687).
Proof. exact (@lem4469383 (s _51686 _51687) (term411 A K t _51686 _51687)). Qed.
Lemma lem4469390 {K : Type'} (k : K -> Prop) (_51686 : K) : (term122 K k _51686) = (term122 K k _51686).
Proof. exact (eq_refl (term122 K k _51686)). Qed.
Lemma lem4469391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term367 A K k t s _51686 _51687) = (term416 A K k s t _51686 _51687).
Proof. exact (MK_COMB (@lem4469390 K k _51686) (@lem4469384 A K s t _51686 _51687)). Qed.
Lemma lem4469395 (q : Prop) (p : Prop) (r : Prop) : (term417 p q r) = (term417 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4469396 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term416 A K k s t _51686 _51687) = (term418 A K s k t _51686 _51687).
Proof. exact (@lem4469395 (s _51686 _51687) (term360 K k _51686) (term411 A K t _51686 _51687)). Qed.
Lemma lem4469412 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term367 A K k t s _51686 _51687) = (term418 A K s k t _51686 _51687).
Proof. exact (TRANS (@lem4469391 A K k s t _51686 _51687) (@lem4469396 A K s k t _51686 _51687)). Qed.
Lemma lem4469413 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4469414 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term419 A K k t s _51686 _51687) = (term420 A K s k t _51686 _51687).
Proof. exact (MK_COMB (@lem4469413) (@lem4469412 A K s k t _51686 _51687)). Qed.
Lemma lem4469430 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term418 A K s k t _51686 _51687) = (term418 A K s k t _51686 _51687).
Proof. exact (eq_refl (term418 A K s k t _51686 _51687)). Qed.
Lemma lem4469431 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : ((term367 A K k t s _51686 _51687) = (term418 A K s k t _51686 _51687)) = ((term418 A K s k t _51686 _51687) = (term418 A K s k t _51686 _51687)).
Proof. exact (MK_COMB (@lem4469414 A K s k t _51686 _51687) (@lem4469430 A K s k t _51686 _51687)). Qed.
Lemma lem4469433 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4469434 (x : Prop) : (x = x) = True.
Proof. exact (@lem4469433 Prop x). Qed.
Lemma lem4469435 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : ((term418 A K s k t _51686 _51687) = (term418 A K s k t _51686 _51687)) = True.
Proof. exact (@lem4469434 (term418 A K s k t _51686 _51687)). Qed.
Lemma lem4469436 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : ((term367 A K k t s _51686 _51687) = (term418 A K s k t _51686 _51687)) = True.
Proof. exact (TRANS (@lem4469431 A K s k t _51686 _51687) (@lem4469435 A K s k t _51686 _51687)). Qed.
Lemma lem4469437 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : True = ((term367 A K k t s _51686 _51687) = (term418 A K s k t _51686 _51687)).
Proof. exact (SYM (@lem4469436 A K s k t _51686 _51687)). Qed.
Lemma lem4469438 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term367 A K k t s _51686 _51687) = (term418 A K s k t _51686 _51687).
Proof. exact (EQ_MP (@lem4469437 A K s k t _51686 _51687) (@lem0)). Qed.
Lemma lem4469439 {A K : Type'} (_51686 : K) (_51687 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term418 A K s k t _51686 _51687.
Proof. exact (EQ_MP (@lem4469438 A K s k t _51686 _51687) (@lem4469160 A K _51686 _51687 k t s i x h1)). Qed.
Lemma lem4469441 (b : Prop) (a : Prop) : (a \/ b) = (term421 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4469442 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51686 : K) (_51687 : A) : (term418 A K s k t _51686 _51687) = (term422 A K k t s _51686 _51687).
Proof. exact (@lem4469441 (term423 A K k t _51686 _51687) (s _51686 _51687)). Qed.
Lemma lem4469444 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4469445 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term426 A K k t _51686 _51687) = (term427 A K k t _51686 _51687).
Proof. exact (@lem4469444 (term360 K k _51686) (term411 A K t _51686 _51687)). Qed.
Lemma lem4469447 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469448 {K : Type'} (k : K -> Prop) (_51686 : K) : (term428 K k _51686) = (k _51686).
Proof. exact (@lem4469447 (k _51686)). Qed.
Lemma lem4469449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4469450 {K : Type'} (k : K -> Prop) (_51686 : K) : (term429 K k _51686) = (term118 K k _51686).
Proof. exact (MK_COMB (@lem4469449) (@lem4469448 K k _51686)). Qed.
Lemma lem4469452 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469453 {A K : Type'} (t : type1470 A K) (_51686 : K) (_51687 : A) : (term430 A K t _51686 _51687) = (t _51686 _51687).
Proof. exact (@lem4469452 (t _51686 _51687)). Qed.
Lemma lem4469454 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term427 A K k t _51686 _51687) = (term431 A K k t _51686 _51687).
Proof. exact (MK_COMB (@lem4469450 K k _51686) (@lem4469453 A K t _51686 _51687)). Qed.
Lemma lem4469455 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term426 A K k t _51686 _51687) = (term431 A K k t _51686 _51687).
Proof. exact (TRANS (@lem4469445 A K k t _51686 _51687) (@lem4469454 A K k t _51686 _51687)). Qed.
Lemma lem4469456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4469457 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51686 : K) (_51687 : A) : (term432 A K k t _51686 _51687) = (term433 A K k t _51686 _51687).
Proof. exact (MK_COMB (@lem4469456) (@lem4469455 A K k t _51686 _51687)). Qed.
Lemma lem4469458 {A K : Type'} (s : type1470 A K) (_51686 : K) (_51687 : A) : (s _51686 _51687) = (s _51686 _51687).
Proof. exact (eq_refl (s _51686 _51687)). Qed.
Lemma lem4469459 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51686 : K) (_51687 : A) : (term422 A K k t s _51686 _51687) = (term434 A K k t s _51686 _51687).
Proof. exact (MK_COMB (@lem4469457 A K k t _51686 _51687) (@lem4469458 A K s _51686 _51687)). Qed.
Lemma lem4469460 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51686 : K) (_51687 : A) : (term418 A K s k t _51686 _51687) = (term434 A K k t s _51686 _51687).
Proof. exact (TRANS (@lem4469442 A K k t s _51686 _51687) (@lem4469459 A K k t s _51686 _51687)). Qed.
Lemma lem4469462 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : term431 A K k t i x.
Proof. exact (conj (@lem4469360 A K k t s i x h1) (@lem4469367 A K t s i x h2)). Qed.
Lemma lem4469464 {A K : Type'} (_51686 : K) (_51687 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k t s _51686 _51687.
Proof. exact (EQ_MP (@lem4469460 A K k t s _51686 _51687) (@lem4469439 A K _51686 _51687 k t s i x h1)). Qed.
Lemma lem4469465 {A K : Type'} (_51686 : K) (_51687 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k t s _51686 _51687.
Proof. exact (@lem4469464 A K _51686 _51687 k t s i x h1). Qed.
Lemma lem4469466 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : term434 A K k t s i x.
Proof. exact (@lem4469465 A K i x k t s i x h1). Qed.
Lemma lem4469469 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : s i x.
Proof. exact (@lem4469466 A K k t s i x h1 (@lem4469462 A K k t s i x h1 h2)). Qed.
Lemma lem4469470 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : term414 A K s i x.
Proof. exact (fun h0 : term411 A K s i x => @lem4469469 A K k t s i x h1 h2). Qed.
Lemma lem4469472 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469473 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term414 A K s i x) = (s i x).
Proof. exact (@lem4469472 (s i x)). Qed.
Lemma lem4469474 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : s i x.
Proof. exact (EQ_MP (@lem4469473 A K s i x) (@lem4469470 A K k t s i x h1 h2)). Qed.
Lemma lem4469477 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4469479 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term411 A K s i x) = (term435 A K s i x).
Proof. exact (@lem4469477 (s i x)). Qed.
Lemma lem4469482 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term105 A K t s i x) : term435 A K s i x.
Proof. exact (EQ_MP (@lem4469479 A K s i x) (@lem4469164 A K t s i x h1)). Qed.
Lemma lem4469485 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : False.
Proof. exact (@lem4469482 A K t s i x h2 (@lem4469474 A K k t s i x h1 h2)). Qed.
Lemma lem4469486 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : term436.
Proof. exact (fun h0 : ~ False => @lem4469485 A K k t s i x h1 h2). Qed.
Lemma lem4469488 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469489 : term436 = False.
Proof. exact (@lem4469488 False). Qed.
Lemma lem4469490 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) (h2 : term105 A K t s i x) : False.
Proof. exact (EQ_MP (@lem4469489) (@lem4469486 A K k t s i x h1 h2)). Qed.
Lemma lem4469492 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : k i.
Proof. exact (proj1 (@lem4468659 A K k s t i x h1)). Qed.
Lemma lem4469493 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term412 K k i.
Proof. exact (fun h0 : term360 K k i => @lem4469492 A K k s t i x h1). Qed.
Lemma lem4469495 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469496 {K : Type'} (k : K -> Prop) (i : K) : (term412 K k i) = (k i).
Proof. exact (@lem4469495 (k i)). Qed.
Lemma lem4469497 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : k i.
Proof. exact (EQ_MP (@lem4469496 K k i) (@lem4469493 A K k s t i x h1)). Qed.
Lemma lem4469499 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : s i x.
Proof. exact (proj1 (@lem4468661 A K k s t i x h1)). Qed.
Lemma lem4469500 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term414 A K s i x.
Proof. exact (fun h0 : term411 A K s i x => @lem4469499 A K k s t i x h1). Qed.
Lemma lem4469502 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469503 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term414 A K s i x) = (s i x).
Proof. exact (@lem4469502 (s i x)). Qed.
Lemma lem4469504 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : s i x.
Proof. exact (EQ_MP (@lem4469503 A K s i x) (@lem4469500 A K k s t i x h1)). Qed.
Lemma lem4469520 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4469521 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term106 A K s t _51688 _51689) = (term415 A K t s _51688 _51689).
Proof. exact (@lem4469520 (t _51688 _51689) (term411 A K s _51688 _51689)). Qed.
Lemma lem4469527 {K : Type'} (k : K -> Prop) (_51688 : K) : (term122 K k _51688) = (term122 K k _51688).
Proof. exact (eq_refl (term122 K k _51688)). Qed.
Lemma lem4469528 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term367 A K k s t _51688 _51689) = (term416 A K k t s _51688 _51689).
Proof. exact (MK_COMB (@lem4469527 K k _51688) (@lem4469521 A K t s _51688 _51689)). Qed.
Lemma lem4469532 (q : Prop) (p : Prop) (r : Prop) : (term417 p q r) = (term417 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4469533 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term416 A K k t s _51688 _51689) = (term418 A K t k s _51688 _51689).
Proof. exact (@lem4469532 (t _51688 _51689) (term360 K k _51688) (term411 A K s _51688 _51689)). Qed.
Lemma lem4469549 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term367 A K k s t _51688 _51689) = (term418 A K t k s _51688 _51689).
Proof. exact (TRANS (@lem4469528 A K k t s _51688 _51689) (@lem4469533 A K t k s _51688 _51689)). Qed.
Lemma lem4469550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4469551 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term419 A K k s t _51688 _51689) = (term420 A K t k s _51688 _51689).
Proof. exact (MK_COMB (@lem4469550) (@lem4469549 A K t k s _51688 _51689)). Qed.
Lemma lem4469567 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term418 A K t k s _51688 _51689) = (term418 A K t k s _51688 _51689).
Proof. exact (eq_refl (term418 A K t k s _51688 _51689)). Qed.
Lemma lem4469568 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : ((term367 A K k s t _51688 _51689) = (term418 A K t k s _51688 _51689)) = ((term418 A K t k s _51688 _51689) = (term418 A K t k s _51688 _51689)).
Proof. exact (MK_COMB (@lem4469551 A K t k s _51688 _51689) (@lem4469567 A K t k s _51688 _51689)). Qed.
Lemma lem4469570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4469571 (x : Prop) : (x = x) = True.
Proof. exact (@lem4469570 Prop x). Qed.
Lemma lem4469572 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : ((term418 A K t k s _51688 _51689) = (term418 A K t k s _51688 _51689)) = True.
Proof. exact (@lem4469571 (term418 A K t k s _51688 _51689)). Qed.
Lemma lem4469573 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : ((term367 A K k s t _51688 _51689) = (term418 A K t k s _51688 _51689)) = True.
Proof. exact (TRANS (@lem4469568 A K t k s _51688 _51689) (@lem4469572 A K t k s _51688 _51689)). Qed.
Lemma lem4469574 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : True = ((term367 A K k s t _51688 _51689) = (term418 A K t k s _51688 _51689)).
Proof. exact (SYM (@lem4469573 A K t k s _51688 _51689)). Qed.
Lemma lem4469575 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term367 A K k s t _51688 _51689) = (term418 A K t k s _51688 _51689).
Proof. exact (EQ_MP (@lem4469574 A K t k s _51688 _51689) (@lem0)). Qed.
Lemma lem4469576 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term418 A K t k s _51688 _51689.
Proof. exact (EQ_MP (@lem4469575 A K t k s _51688 _51689) (@lem4469180 A K _51688 _51689 i x k t s h1)). Qed.
Lemma lem4469578 (b : Prop) (a : Prop) : (a \/ b) = (term421 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4469579 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51688 : K) (_51689 : A) : (term418 A K t k s _51688 _51689) = (term422 A K k s t _51688 _51689).
Proof. exact (@lem4469578 (term423 A K k s _51688 _51689) (t _51688 _51689)). Qed.
Lemma lem4469581 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4469582 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term426 A K k s _51688 _51689) = (term427 A K k s _51688 _51689).
Proof. exact (@lem4469581 (term360 K k _51688) (term411 A K s _51688 _51689)). Qed.
Lemma lem4469584 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469585 {K : Type'} (k : K -> Prop) (_51688 : K) : (term428 K k _51688) = (k _51688).
Proof. exact (@lem4469584 (k _51688)). Qed.
Lemma lem4469586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4469587 {K : Type'} (k : K -> Prop) (_51688 : K) : (term429 K k _51688) = (term118 K k _51688).
Proof. exact (MK_COMB (@lem4469586) (@lem4469585 K k _51688)). Qed.
Lemma lem4469589 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469590 {A K : Type'} (s : type1470 A K) (_51688 : K) (_51689 : A) : (term430 A K s _51688 _51689) = (s _51688 _51689).
Proof. exact (@lem4469589 (s _51688 _51689)). Qed.
Lemma lem4469591 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term427 A K k s _51688 _51689) = (term431 A K k s _51688 _51689).
Proof. exact (MK_COMB (@lem4469587 K k _51688) (@lem4469590 A K s _51688 _51689)). Qed.
Lemma lem4469592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term426 A K k s _51688 _51689) = (term431 A K k s _51688 _51689).
Proof. exact (TRANS (@lem4469582 A K k s _51688 _51689) (@lem4469591 A K k s _51688 _51689)). Qed.
Lemma lem4469593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4469594 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_51688 : K) (_51689 : A) : (term432 A K k s _51688 _51689) = (term433 A K k s _51688 _51689).
Proof. exact (MK_COMB (@lem4469593) (@lem4469592 A K k s _51688 _51689)). Qed.
Lemma lem4469595 {A K : Type'} (t : type1470 A K) (_51688 : K) (_51689 : A) : (t _51688 _51689) = (t _51688 _51689).
Proof. exact (eq_refl (t _51688 _51689)). Qed.
Lemma lem4469596 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51688 : K) (_51689 : A) : (term422 A K k s t _51688 _51689) = (term434 A K k s t _51688 _51689).
Proof. exact (MK_COMB (@lem4469594 A K k s _51688 _51689) (@lem4469595 A K t _51688 _51689)). Qed.
Lemma lem4469597 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51688 : K) (_51689 : A) : (term418 A K t k s _51688 _51689) = (term434 A K k s t _51688 _51689).
Proof. exact (TRANS (@lem4469579 A K k s t _51688 _51689) (@lem4469596 A K k s t _51688 _51689)). Qed.
Lemma lem4469599 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term431 A K k s i x.
Proof. exact (conj (@lem4469497 A K k s t i x h1) (@lem4469504 A K k s t i x h1)). Qed.
Lemma lem4469601 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k s t _51688 _51689.
Proof. exact (EQ_MP (@lem4469597 A K k s t _51688 _51689) (@lem4469576 A K _51688 _51689 i x k t s h1)). Qed.
Lemma lem4469602 {A K : Type'} (_51688 : K) (_51689 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k s t _51688 _51689.
Proof. exact (@lem4469601 A K _51688 _51689 i x k t s h1). Qed.
Lemma lem4469603 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k s t i x.
Proof. exact (@lem4469602 A K i x i x k t s h1). Qed.
Lemma lem4469606 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : t i x.
Proof. exact (@lem4469603 A K i x k t s h2 (@lem4469599 A K k s t i x h1)). Qed.
Lemma lem4469607 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : term414 A K t i x.
Proof. exact (fun h0 : term411 A K t i x => @lem4469606 A K i x k t s h1 h2). Qed.
Lemma lem4469609 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469610 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term414 A K t i x) = (t i x).
Proof. exact (@lem4469609 (t i x)). Qed.
Lemma lem4469611 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : t i x.
Proof. exact (EQ_MP (@lem4469610 A K t i x) (@lem4469607 A K i x k t s h1 h2)). Qed.
Lemma lem4469614 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4469616 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term411 A K t i x) = (term435 A K t i x).
Proof. exact (@lem4469614 (t i x)). Qed.
Lemma lem4469619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) (h1 : term241 A K k s t i x) : term435 A K t i x.
Proof. exact (EQ_MP (@lem4469616 A K t i x) (@lem4469170 A K k s t i x h1)). Qed.
Lemma lem4469622 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : False.
Proof. exact (@lem4469619 A K k s t i x h1 (@lem4469611 A K i x k t s h1 h2)). Qed.
Lemma lem4469623 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : term436.
Proof. exact (fun h0 : ~ False => @lem4469622 A K i x k t s h1 h2). Qed.
Lemma lem4469625 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469626 : term436 = False.
Proof. exact (@lem4469625 False). Qed.
Lemma lem4469627 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k s t i x) (h2 : term311 A K i x k t s) : False.
Proof. exact (EQ_MP (@lem4469626) (@lem4469623 A K i x k t s h1 h2)). Qed.
Lemma lem4469629 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : k i.
Proof. exact (proj1 (@lem4468660 A K k t s i x h1)). Qed.
Lemma lem4469630 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term412 K k i.
Proof. exact (fun h0 : term360 K k i => @lem4469629 A K k t s i x h1). Qed.
Lemma lem4469632 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469633 {K : Type'} (k : K -> Prop) (i : K) : (term412 K k i) = (k i).
Proof. exact (@lem4469632 (k i)). Qed.
Lemma lem4469634 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : k i.
Proof. exact (EQ_MP (@lem4469633 K k i) (@lem4469630 A K k t s i x h1)). Qed.
Lemma lem4469636 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : t i x.
Proof. exact (proj1 (@lem4468665 A K k t s i x h1)). Qed.
Lemma lem4469637 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term414 A K t i x.
Proof. exact (fun h0 : term411 A K t i x => @lem4469636 A K k t s i x h1). Qed.
Lemma lem4469639 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469640 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term414 A K t i x) = (t i x).
Proof. exact (@lem4469639 (t i x)). Qed.
Lemma lem4469641 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : t i x.
Proof. exact (EQ_MP (@lem4469640 A K t i x) (@lem4469637 A K k t s i x h1)). Qed.
Lemma lem4469657 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4469658 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term106 A K t s _51690 _51691) = (term415 A K s t _51690 _51691).
Proof. exact (@lem4469657 (s _51690 _51691) (term411 A K t _51690 _51691)). Qed.
Lemma lem4469664 {K : Type'} (k : K -> Prop) (_51690 : K) : (term122 K k _51690) = (term122 K k _51690).
Proof. exact (eq_refl (term122 K k _51690)). Qed.
Lemma lem4469665 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term367 A K k t s _51690 _51691) = (term416 A K k s t _51690 _51691).
Proof. exact (MK_COMB (@lem4469664 K k _51690) (@lem4469658 A K s t _51690 _51691)). Qed.
Lemma lem4469669 (q : Prop) (p : Prop) (r : Prop) : (term417 p q r) = (term417 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4469670 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term416 A K k s t _51690 _51691) = (term418 A K s k t _51690 _51691).
Proof. exact (@lem4469669 (s _51690 _51691) (term360 K k _51690) (term411 A K t _51690 _51691)). Qed.
Lemma lem4469686 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term367 A K k t s _51690 _51691) = (term418 A K s k t _51690 _51691).
Proof. exact (TRANS (@lem4469665 A K k s t _51690 _51691) (@lem4469670 A K s k t _51690 _51691)). Qed.
Lemma lem4469687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4469688 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term419 A K k t s _51690 _51691) = (term420 A K s k t _51690 _51691).
Proof. exact (MK_COMB (@lem4469687) (@lem4469686 A K s k t _51690 _51691)). Qed.
Lemma lem4469704 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term418 A K s k t _51690 _51691) = (term418 A K s k t _51690 _51691).
Proof. exact (eq_refl (term418 A K s k t _51690 _51691)). Qed.
Lemma lem4469705 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : ((term367 A K k t s _51690 _51691) = (term418 A K s k t _51690 _51691)) = ((term418 A K s k t _51690 _51691) = (term418 A K s k t _51690 _51691)).
Proof. exact (MK_COMB (@lem4469688 A K s k t _51690 _51691) (@lem4469704 A K s k t _51690 _51691)). Qed.
Lemma lem4469707 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4469708 (x : Prop) : (x = x) = True.
Proof. exact (@lem4469707 Prop x). Qed.
Lemma lem4469709 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : ((term418 A K s k t _51690 _51691) = (term418 A K s k t _51690 _51691)) = True.
Proof. exact (@lem4469708 (term418 A K s k t _51690 _51691)). Qed.
Lemma lem4469710 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : ((term367 A K k t s _51690 _51691) = (term418 A K s k t _51690 _51691)) = True.
Proof. exact (TRANS (@lem4469705 A K s k t _51690 _51691) (@lem4469709 A K s k t _51690 _51691)). Qed.
Lemma lem4469711 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : True = ((term367 A K k t s _51690 _51691) = (term418 A K s k t _51690 _51691)).
Proof. exact (SYM (@lem4469710 A K s k t _51690 _51691)). Qed.
Lemma lem4469712 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term367 A K k t s _51690 _51691) = (term418 A K s k t _51690 _51691).
Proof. exact (EQ_MP (@lem4469711 A K s k t _51690 _51691) (@lem0)). Qed.
Lemma lem4469713 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term418 A K s k t _51690 _51691.
Proof. exact (EQ_MP (@lem4469712 A K s k t _51690 _51691) (@lem4469216 A K _51690 _51691 i x k t s h1)). Qed.
Lemma lem4469715 (b : Prop) (a : Prop) : (a \/ b) = (term421 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4469716 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51690 : K) (_51691 : A) : (term418 A K s k t _51690 _51691) = (term422 A K k t s _51690 _51691).
Proof. exact (@lem4469715 (term423 A K k t _51690 _51691) (s _51690 _51691)). Qed.
Lemma lem4469718 (a : Prop) (b : Prop) : (term424 a b) = (term425 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4469719 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term426 A K k t _51690 _51691) = (term427 A K k t _51690 _51691).
Proof. exact (@lem4469718 (term360 K k _51690) (term411 A K t _51690 _51691)). Qed.
Lemma lem4469721 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469722 {K : Type'} (k : K -> Prop) (_51690 : K) : (term428 K k _51690) = (k _51690).
Proof. exact (@lem4469721 (k _51690)). Qed.
Lemma lem4469723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4469724 {K : Type'} (k : K -> Prop) (_51690 : K) : (term429 K k _51690) = (term118 K k _51690).
Proof. exact (MK_COMB (@lem4469723) (@lem4469722 K k _51690)). Qed.
Lemma lem4469726 (a : Prop) : (term101 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4469727 {A K : Type'} (t : type1470 A K) (_51690 : K) (_51691 : A) : (term430 A K t _51690 _51691) = (t _51690 _51691).
Proof. exact (@lem4469726 (t _51690 _51691)). Qed.
Lemma lem4469728 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term427 A K k t _51690 _51691) = (term431 A K k t _51690 _51691).
Proof. exact (MK_COMB (@lem4469724 K k _51690) (@lem4469727 A K t _51690 _51691)). Qed.
Lemma lem4469729 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term426 A K k t _51690 _51691) = (term431 A K k t _51690 _51691).
Proof. exact (TRANS (@lem4469719 A K k t _51690 _51691) (@lem4469728 A K k t _51690 _51691)). Qed.
Lemma lem4469730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4469731 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_51690 : K) (_51691 : A) : (term432 A K k t _51690 _51691) = (term433 A K k t _51690 _51691).
Proof. exact (MK_COMB (@lem4469730) (@lem4469729 A K k t _51690 _51691)). Qed.
Lemma lem4469732 {A K : Type'} (s : type1470 A K) (_51690 : K) (_51691 : A) : (s _51690 _51691) = (s _51690 _51691).
Proof. exact (eq_refl (s _51690 _51691)). Qed.
Lemma lem4469733 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51690 : K) (_51691 : A) : (term422 A K k t s _51690 _51691) = (term434 A K k t s _51690 _51691).
Proof. exact (MK_COMB (@lem4469731 A K k t _51690 _51691) (@lem4469732 A K s _51690 _51691)). Qed.
Lemma lem4469734 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_51690 : K) (_51691 : A) : (term418 A K s k t _51690 _51691) = (term434 A K k t s _51690 _51691).
Proof. exact (TRANS (@lem4469716 A K k t s _51690 _51691) (@lem4469733 A K k t s _51690 _51691)). Qed.
Lemma lem4469736 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term431 A K k t i x.
Proof. exact (conj (@lem4469634 A K k t s i x h1) (@lem4469641 A K k t s i x h1)). Qed.
Lemma lem4469738 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k t s _51690 _51691.
Proof. exact (EQ_MP (@lem4469734 A K k t s _51690 _51691) (@lem4469713 A K _51690 _51691 i x k t s h1)). Qed.
Lemma lem4469739 {A K : Type'} (_51690 : K) (_51691 : A) (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k t s _51690 _51691.
Proof. exact (@lem4469738 A K _51690 _51691 i x k t s h1). Qed.
Lemma lem4469740 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : term434 A K k t s i x.
Proof. exact (@lem4469739 A K i x i x k t s h1). Qed.
Lemma lem4469743 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : s i x.
Proof. exact (@lem4469740 A K i x k t s h2 (@lem4469736 A K k t s i x h1)). Qed.
Lemma lem4469744 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : term414 A K s i x.
Proof. exact (fun h0 : term411 A K s i x => @lem4469743 A K i x k t s h1 h2). Qed.
Lemma lem4469746 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469747 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term414 A K s i x) = (s i x).
Proof. exact (@lem4469746 (s i x)). Qed.
Lemma lem4469748 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : s i x.
Proof. exact (EQ_MP (@lem4469747 A K s i x) (@lem4469744 A K i x k t s h1 h2)). Qed.
Lemma lem4469751 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4469753 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term411 A K s i x) = (term435 A K s i x).
Proof. exact (@lem4469751 (s i x)). Qed.
Lemma lem4469756 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term241 A K k t s i x) : term435 A K s i x.
Proof. exact (EQ_MP (@lem4469753 A K s i x) (@lem4469196 A K k t s i x h1)). Qed.
Lemma lem4469759 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : False.
Proof. exact (@lem4469756 A K k t s i x h1 (@lem4469748 A K i x k t s h1 h2)). Qed.
Lemma lem4469760 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : term436.
Proof. exact (fun h0 : ~ False => @lem4469759 A K i x k t s h1 h2). Qed.
Lemma lem4469762 (p : Prop) : (term413 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4469763 : term436 = False.
Proof. exact (@lem4469762 False). Qed.
Lemma lem4469764 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term241 A K k t s i x) (h2 : term311 A K i x k t s) : False.
Proof. exact (EQ_MP (@lem4469763) (@lem4469760 A K i x k t s h1 h2)). Qed.
Lemma lem4469765 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term311 A K i x k t s) : False.
Proof. exact (or_elim (@lem4468658 A K i x k t s h1) (fun h0 : term241 A K k s t i x => @lem4469627 A K i x k t s h0 h1) (fun h0 : term241 A K k t s i x => @lem4469764 A K i x k t s h0 h1)). Qed.
Lemma lem4469766 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) (h1 : term229 A K k t s i x) : False.
Proof. exact (or_elim (@lem4468647 A K k t s i x h1) (fun h0 : term105 A K s t i x => @lem4469353 A K k s t i x h1 h0) (fun h0 : term105 A K t s i x => @lem4469490 A K k t s i x h1 h0)). Qed.
Lemma lem4469767 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term350 A K i x k t s) : False.
Proof. exact (or_elim (@lem4468642 A K i x k t s h1) (fun h0 : term229 A K k t s i x => @lem4469766 A K k t s i x h0) (fun h0 : term311 A K i x k t s => @lem4469765 A K i x k t s h0)). Qed.
Lemma lem4469768 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term350 A K i x k t s) : (term350 A K i x k t s) = False.
Proof. exact (prop_ext (fun h2 : term350 A K i x k t s => @lem4469767 A K i x k t s h1) (fun h2 : False => @lem4468642 A K i x k t s h1)). Qed.
Lemma lem4469769 {A K : Type'} (i : K) (x : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term350 A K i x k t s) : False.
Proof. exact (EQ_MP (@lem4469768 A K i x k t s h1) (@lem4468642 A K i x k t s h1)). Qed.
Lemma lem4469770 {A K : Type'} (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term353 A K i k t s) : False.
Proof. exact (ex_elim (@lem4468436 A K i k t s h1) (fun x : A => fun h0 : term352 A K i k t s x => @lem4469769 A K i x k t s h0)). Qed.
Lemma lem4469771 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term103 A K k t s) : False.
Proof. exact (ex_elim (@lem4468435 A K k t s h1) (fun i : K => fun h0 : term354 A K k t s i => @lem4469770 A K i k t s h0)). Qed.
Lemma lem4469772 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term103 A K k t s) : (term103 A K k t s) = False.
Proof. exact (prop_ext (fun h2 : term103 A K k t s => @lem4469771 A K k t s h1) (fun h2 : False => @lem4467282 A K k t s h1)). Qed.
Lemma lem4469773 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term103 A K k t s) : False.
Proof. exact (EQ_MP (@lem4469772 A K k t s h1) (@lem4467282 A K k t s h1)). Qed.
Lemma lem4469774 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term102 A K k t s.
Proof. exact (fun h0 : term103 A K k t s => @lem4469773 A K k t s h0). Qed.
Lemma lem4469775 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term81 A K k t s) = (term87 A K k t s).
Proof. exact (EQ_MP (@lem4467281 A K k t s) (@lem4469774 A K k t s)). Qed.
Lemma lem4469780 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term89 A K k s.
Proof. exact (fun t : type1470 A K => @lem4469775 A K k t s). Qed.
Lemma lem4469785 {A K : Type'} (k : K -> Prop) : term91 A K k.
Proof. exact (fun s : type1470 A K => @lem4469780 A K k s). Qed.
Lemma lem4469790 {A K : Type'} : term93 A K.
Proof. exact (fun k : K -> Prop => @lem4469785 A K k). Qed.
Lemma lem4469791 {A K : Type'} : term95 A K.
Proof. exact (EQ_MP (@lem4467277 A K) (@lem4469790 A K)). Qed.
Lemma lem4469793 {A K : Type'} : term95 A K.
Proof. exact (@lem4467055 A K (@lem4469791 A K)). Qed.
Lemma lem4469794 {A K : Type'} (h1 : term96 A K) : False.
Proof. exact (@lem4469793 A K (@lem4467039 A K h1)). Qed.
Lemma lem4469795 {A K : Type'} (h1 : term96 A K) : (term96 A K) = False.
Proof. exact (prop_ext (fun h2 : term96 A K => @lem4469794 A K h1) (fun h2 : False => @lem4467039 A K h1)). Qed.
Lemma lem4469796 {A K : Type'} (h1 : term96 A K) : False.
Proof. exact (EQ_MP (@lem4469795 A K h1) (@lem4467039 A K h1)). Qed.
Lemma lem4469797 {A K : Type'} : term95 A K.
Proof. exact (fun h0 : term96 A K => @lem4469796 A K h0). Qed.
Lemma lem4469798 {A K : Type'} : term93 A K.
Proof. exact (EQ_MP (@lem4467038 A K) (@lem4469797 A K)). Qed.
Lemma lem4469799 {A K : Type'} : term67 A K.
Proof. exact (EQ_MP (@lem4467034 A K) (@lem4469798 A K)). Qed.
Lemma lem4469800 {A K : Type'} : term44 A K.
Proof. exact (EQ_MP (@lem4466809 A K) (@lem4469799 A K)). Qed.
Lemma lem4469801 {A K : Type'} : term43 A K.
Proof. exact (EQ_MP (@lem4466659 A K) (@lem4469800 A K)). Qed.
