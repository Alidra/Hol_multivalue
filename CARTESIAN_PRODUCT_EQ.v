Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import EXTENSION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUBSET_ANTISYM_EQ_spec.
Require Import SUBSET_CARTESIAN_PRODUCT_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1832_spec.
Require Import thm1833_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4426551 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (term0 A t s) = (s = t).
Proof. exact (h1). Qed.
Lemma lem4426552 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : (term0 A t s) = (s = t)) : (s = t) = (term0 A t s).
Proof. exact (SYM (@lem4426551 A s t h1)). Qed.
Lemma lem4426553 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (s = t) = (term0 A t s).
Proof. exact (h1). Qed.
Lemma lem4426554 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : (s = t) = (term0 A t s)) : (term0 A t s) = (s = t).
Proof. exact (SYM (@lem4426553 A t s h1)). Qed.
Lemma lem4426555 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term0 A t s) = (s = t)) = ((s = t) = (term0 A t s)).
Proof. exact (prop_ext (fun h1 : (term0 A t s) = (s = t) => @lem4426552 A s t h1) (fun h1 : (s = t) = (term0 A t s) => @lem4426554 A t s h1)). Qed.
Lemma lem4426556 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4426555 A t s)). Qed.
Lemma lem4426557 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4426558 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (MK_COMB (@lem4426557 A) (@lem4426556 A s)). Qed.
Lemma lem4426559 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4426558 A s)). Qed.
Lemma lem4426560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4426561 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4426560 A) (@lem4426559 A)). Qed.
Lemma lem4426562 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4426561 A) (@lem3219910 A)). Qed.
Lemma lem4426563 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term9 A K k s.
Proof. exact (@lem9784 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4426564 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term9 A K k s) = (term10 A K k s).
Proof. exact (eq_refl (term9 A K k s)). Qed.
Lemma lem4426565 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term10 A K k s.
Proof. exact (EQ_MP (@lem4426564 A K k s) (@lem4426563 A K k s)). Qed.
Lemma lem4426567 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : term11 A K k s.
Proof. exact (h1). Qed.
Lemma lem4426568 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term9 A K k t.
Proof. exact (@lem9784 ((@cartesian_product A K k t) = (@EMPTY (K -> A)))). Qed.
Lemma lem4426569 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term9 A K k t) = (term10 A K k t).
Proof. exact (eq_refl (term9 A K k t)). Qed.
Lemma lem4426570 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term10 A K k t.
Proof. exact (EQ_MP (@lem4426569 A K k t) (@lem4426568 A K k t)). Qed.
Lemma lem4426572 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : term11 A K k t.
Proof. exact (h1). Qed.
Lemma lem4426573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term12 A K k s t.
Proof. exact (@lem9784 (term13 A K k s t)). Qed.
Lemma lem4426574 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term12 A K k s t) = (term14 A K k s t).
Proof. exact (eq_refl (term12 A K k s t)). Qed.
Lemma lem4426575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term14 A K k s t.
Proof. exact (EQ_MP (@lem4426574 A K k s t) (@lem4426573 A K k s t)). Qed.
Lemma lem4426576 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term13 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4426577 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : term15 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4426578 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term16 A K k s t i.
Proof. exact (@lem4426576 A K k s t h1 i). Qed.
Lemma lem4426579 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term16 A K k s t i) = (term17 A K k s t i).
Proof. exact (eq_refl (term16 A K k s t i)). Qed.
Lemma lem4426580 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term17 A K k s t i.
Proof. exact (EQ_MP (@lem4426579 A K k s t i) (@lem4426578 A K i k s t h1)). Qed.
Lemma lem4426581 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term17 A K k s t i) = ((term17 A K k s t i) = True).
Proof. exact (@lem7 (term17 A K k s t i)). Qed.
Lemma lem4426600 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term17 A K k s t i) = True.
Proof. exact (EQ_MP (@lem4426581 A K k s t i) (@lem4426580 A K i k s t h1)). Qed.
Lemma lem4426601 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term17 A K k s t i) = True.
Proof. exact (@lem4426600 A K i k s t h1). Qed.
Lemma lem4426602 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term18 A K k s t) = (term19 K).
Proof. exact (fun_ext (fun i : K => @lem4426601 A K i k s t h1)). Qed.
Lemma lem4426603 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4426604 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term13 A K k s t) = (term20 K).
Proof. exact (MK_COMB (@lem4426603 K) (@lem4426602 A K k s t h1)). Qed.
Lemma lem4426606 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4426607 {K : Type'} (t : Prop) : (term21 K t) = t.
Proof. exact (@lem4426606 K t). Qed.
Lemma lem4426608 {K : Type'} : (term20 K) = True.
Proof. exact (@lem4426607 K True). Qed.
Lemma lem4426609 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term13 A K k s t) = True.
Proof. exact (TRANS (@lem4426604 A K k s t h1) (@lem4426608 K)). Qed.
Lemma lem4426610 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term22 A K s k t) = (term22 A K s k t).
Proof. exact (eq_refl (term22 A K s k t)). Qed.
Lemma lem4426611 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term23 A K k s t) = (term24 A K s k t).
Proof. exact (MK_COMB (@lem4426610 A K s k t) (@lem4426609 A K k s t h1)). Qed.
Lemma lem4426613 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4426614 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term24 A K s k t) = True.
Proof. exact (@lem4426613 (term25 A K s k t)). Qed.
Lemma lem4426615 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term23 A K k s t) = True.
Proof. exact (TRANS (@lem4426611 A K k s t h1) (@lem4426614 A K s k t)). Qed.
Lemma lem4426616 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term26 A K s k t) = (term26 A K s k t).
Proof. exact (eq_refl (term26 A K s k t)). Qed.
Lemma lem4426617 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t)) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = True).
Proof. exact (MK_COMB (@lem4426616 A K s k t) (@lem4426615 A K k s t h1)). Qed.
Lemma lem4426619 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem4426620 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = True) = ((@cartesian_product A K k s) = (@cartesian_product A K k t)).
Proof. exact (@lem4426619 ((@cartesian_product A K k s) = (@cartesian_product A K k t))). Qed.
Lemma lem4426623 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t)) = ((@cartesian_product A K k s) = (@cartesian_product A K k t)).
Proof. exact (TRANS (@lem4426617 A K k s t h1) (@lem4426620 A K s k t)). Qed.
Lemma lem4426624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t)).
Proof. exact (SYM (@lem4426623 A K k s t h1)). Qed.
Lemma lem4426625 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term27 A K k s t.
Proof. exact (@lem82 (term13 A K k s t)). Qed.
Lemma lem4426640 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (term13 A K k s t) = False.
Proof. exact (@lem4426625 A K k s t (@lem4426577 A K k s t h1)). Qed.
Lemma lem4426641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (term13 A K k s t) = False.
Proof. exact (@lem4426640 A K k s t h1). Qed.
Lemma lem4426642 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term22 A K s k t) = (term22 A K s k t).
Proof. exact (eq_refl (term22 A K s k t)). Qed.
Lemma lem4426643 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (term23 A K k s t) = (term28 A K s k t).
Proof. exact (MK_COMB (@lem4426642 A K s k t) (@lem4426641 A K k s t h1)). Qed.
Lemma lem4426645 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem4426646 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term28 A K s k t) = (term25 A K s k t).
Proof. exact (@lem4426645 (term25 A K s k t)). Qed.
Lemma lem4426653 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (term23 A K k s t) = (term25 A K s k t).
Proof. exact (TRANS (@lem4426643 A K k s t h1) (@lem4426646 A K s k t)). Qed.
Lemma lem4426654 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term26 A K s k t) = (term26 A K s k t).
Proof. exact (eq_refl (term26 A K s k t)). Qed.
Lemma lem4426655 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t)) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)).
Proof. exact (MK_COMB (@lem4426654 A K s k t) (@lem4426653 A K k s t h1)). Qed.
Lemma lem4426658 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t)).
Proof. exact (SYM (@lem4426655 A K k s t h1)). Qed.
Lemma lem4426683 {_83095 : Type'} : term29 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4426684 {_83095 : Type'} (p : _83095 -> Prop) : term30 _83095 p.
Proof. exact (@lem4426683 _83095 p). Qed.
Lemma lem4426685 {_83095 : Type'} (p : _83095 -> Prop) : (term30 _83095 p) = (term31 _83095 p).
Proof. exact (eq_refl (term30 _83095 p)). Qed.
Lemma lem4426686 {_83095 : Type'} (p : _83095 -> Prop) : term31 _83095 p.
Proof. exact (EQ_MP (@lem4426685 _83095 p) (@lem4426684 _83095 p)). Qed.
Lemma lem4426687 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term32 _83095 p x.
Proof. exact (@lem4426686 _83095 p x). Qed.
Lemma lem4426688 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term32 _83095 p x) = ((term33 _83095 x p) = (p x)).
Proof. exact (eq_refl (term32 _83095 p x)). Qed.
Lemma lem4426697 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4426698 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4426699 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (EQ_MP (@lem4426698 A s) (@lem4426697 A s)). Qed.
Lemma lem4426700 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (@lem4426699 A s t). Qed.
Lemma lem4426701 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = ((s = t) = (term37 A s t)).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem4426703 {A K : Type'} (k : K -> Prop) : term38 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4426704 {A K : Type'} (k : K -> Prop) : (term38 A K k) = (term39 A K k).
Proof. exact (eq_refl (term38 A K k)). Qed.
Lemma lem4426705 {A K : Type'} (k : K -> Prop) : term39 A K k.
Proof. exact (EQ_MP (@lem4426704 A K k) (@lem4426703 A K k)). Qed.
Lemma lem4426706 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term40 A K k s.
Proof. exact (@lem4426705 A K k s). Qed.
Lemma lem4426707 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term40 A K k s) = ((@cartesian_product A K k s) = (term41 A K k s)).
Proof. exact (eq_refl (term40 A K k s)). Qed.
Lemma lem4426709 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term16 A K k s t i.
Proof. exact (@lem4426576 A K k s t h1 i). Qed.
Lemma lem4426710 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term16 A K k s t i) = (term17 A K k s t i).
Proof. exact (eq_refl (term16 A K k s t i)). Qed.
Lemma lem4426711 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term17 A K k s t i.
Proof. exact (EQ_MP (@lem4426710 A K k s t i) (@lem4426709 A K i k s t h1)). Qed.
Lemma lem4426712 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4426713 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term13 A K k s t) (h2 : @IN K i k) : (s i) = (t i).
Proof. exact (@lem4426711 A K i k s t h1 (@lem4426712 K i k h2)). Qed.
Lemma lem4426722 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem4426701 A s t) (@lem4426700 A s t)). Qed.
Lemma lem4426723 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term42 A K s t).
Proof. exact (@lem4426722 (K -> A) s t). Qed.
Lemma lem4426724 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term43 A K s k t).
Proof. exact (@lem4426723 A K (@cartesian_product A K k s) (@cartesian_product A K k t)). Qed.
Lemma lem4426734 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term41 A K k s).
Proof. exact (EQ_MP (@lem4426707 A K k s) (@lem4426706 A K k s)). Qed.
Lemma lem4426735 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term41 A K k s).
Proof. exact (@lem4426734 A K k s). Qed.
Lemma lem4426749 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term44 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4426750 (p : Prop) (q : Prop) (p' : Prop) : term45 p q p'.
Proof. exact (fun q' : Prop => @lem4426749 p q p' q'). Qed.
Lemma lem4426751 (p : Prop) (q : Prop) : term46 p q.
Proof. exact (fun p' : Prop => @lem4426750 p q p'). Qed.
Lemma lem4426752 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : term47 A K k f s i.
Proof. exact (@lem4426751 (@IN K i k) (term48 A K f s i)). Qed.
Lemma lem4426753 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term49 A K k f s i p'.
Proof. exact (@lem4426752 A K k f s i p'). Qed.
Lemma lem4426754 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : (term49 A K k f s i p') = (term50 A K k f s i p').
Proof. exact (eq_refl (term49 A K k f s i p')). Qed.
Lemma lem4426755 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) : term50 A K k f s i p'.
Proof. exact (EQ_MP (@lem4426754 A K k f s i p') (@lem4426753 A K k f s i p')). Qed.
Lemma lem4426756 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term51 A K k f s i p' q'.
Proof. exact (@lem4426755 A K k f s i p' q'). Qed.
Lemma lem4426757 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : (term51 A K k f s i p' q') = (term52 A K k f s i p' q').
Proof. exact (eq_refl (term51 A K k f s i p' q')). Qed.
Lemma lem4426758 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) (p' : Prop) (q' : Prop) : term52 A K k f s i p' q'.
Proof. exact (EQ_MP (@lem4426757 A K k f s i p' q') (@lem4426756 A K k f s i p' q')). Qed.
Lemma lem4426759 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = (@IN K i k).
Proof. exact (eq_refl (@IN K i k)). Qed.
Lemma lem4426760 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term53 A K f s i k q'.
Proof. exact (@lem4426758 A K k f s i (@IN K i k) q'). Qed.
Lemma lem4426761 {A K : Type'} (f : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (q' : Prop) : term54 A K f s i k q'.
Proof. exact (@lem4426760 A K f s i k q' (@lem4426759 K i k)). Qed.
Lemma lem4426762 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem4426763 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem4426766 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term17 A K k s t i.
Proof. exact (fun h0 : @IN K i k => @lem4426713 A K s t i k h1 h0). Qed.
Lemma lem4426767 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term17 A K k s t i.
Proof. exact (@lem4426766 A K i k s t h1). Qed.
Lemma lem4426769 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem4426763 K i k) (@lem4426762 K i k h1)). Qed.
Lemma lem4426770 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : True = (@IN K i k).
Proof. exact (SYM (@lem4426769 K i k h1)). Qed.
Lemma lem4426771 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (EQ_MP (@lem4426770 K i k h1) (@lem0)). Qed.
Lemma lem4426772 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term13 A K k s t) (h2 : @IN K i k) : (s i) = (t i).
Proof. exact (@lem4426767 A K i k s t h1 (@lem4426771 K i k h2)). Qed.
Lemma lem4426773 {A K : Type'} (f : K -> A) (i : K) : (term55 A K f i) = (term55 A K f i).
Proof. exact (eq_refl (term55 A K f i)). Qed.
Lemma lem4426774 {A K : Type'} (f : K -> A) (s : type1470 A K) (t : type1470 A K) (i : K) (k : K -> Prop) (h1 : term13 A K k s t) (h2 : @IN K i k) : (term48 A K f s i) = (term48 A K f t i).
Proof. exact (MK_COMB (@lem4426773 A K f i) (@lem4426772 A K s t i k h1 h2)). Qed.
Lemma lem4426775 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : term56 A K k s f t i.
Proof. exact (fun h0 : @IN K i k => @lem4426774 A K f s t i k h1 h0). Qed.
Lemma lem4426776 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (t : type1470 A K) (i : K) : term57 A K s k f t i.
Proof. exact (@lem4426761 A K f s i k (term48 A K f t i)). Qed.
Lemma lem4426777 {A K : Type'} (f : K -> A) (i : K) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term58 A K k f s i) = (term58 A K k f t i).
Proof. exact (@lem4426776 A K s k f t i (@lem4426775 A K f i k s t h1)). Qed.
Lemma lem4426801 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term59 A K k f s) = (term59 A K k f t).
Proof. exact (fun_ext (fun i : K => @lem4426777 A K f i k s t h1)). Qed.
Lemma lem4426825 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4426826 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term60 A K k f s) = (term60 A K k f t).
Proof. exact (MK_COMB (@lem4426825 K) (@lem4426801 A K f k s t h1)). Qed.
Lemma lem4426854 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term61 A K k f) = (term61 A K k f).
Proof. exact (eq_refl (term61 A K k f)). Qed.
Lemma lem4426855 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term62 A K k f s) = (term62 A K k f t).
Proof. exact (MK_COMB (@lem4426854 A K k f) (@lem4426826 A K f k s t h1)). Qed.
Lemma lem4426885 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4426886 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term63 A K GEN_PVAR_140 k f s) = (term63 A K GEN_PVAR_140 k f t).
Proof. exact (MK_COMB (@lem4426885 A K GEN_PVAR_140) (@lem4426855 A K f k s t h1)). Qed.
Lemma lem4426916 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4426917 {A K : Type'} (GEN_PVAR_140 : K -> A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term64 A K GEN_PVAR_140 k s f) = (term64 A K GEN_PVAR_140 k t f).
Proof. exact (MK_COMB (@lem4426886 A K GEN_PVAR_140 f k s t h1) (@lem4426916 A K f)). Qed.
Lemma lem4426947 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term65 A K GEN_PVAR_140 k s) = (term65 A K GEN_PVAR_140 k t).
Proof. exact (fun_ext (fun f : K -> A => @lem4426917 A K GEN_PVAR_140 f k s t h1)). Qed.
Lemma lem4426977 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4426978 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term66 A K GEN_PVAR_140 k s) = (term66 A K GEN_PVAR_140 k t).
Proof. exact (MK_COMB (@lem4426977 A K) (@lem4426947 A K GEN_PVAR_140 k s t h1)). Qed.
Lemma lem4427012 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term67 A K k s) = (term67 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4426978 A K GEN_PVAR_140 k s t h1)). Qed.
Lemma lem4427046 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4427047 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term41 A K k s) = (term41 A K k t).
Proof. exact (MK_COMB (@lem4427046 A K) (@lem4427012 A K k s t h1)). Qed.
Lemma lem4427081 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (@cartesian_product A K k s) = (term41 A K k t).
Proof. exact (TRANS (@lem4426735 A K k s) (@lem4427047 A K k s t h1)). Qed.
Lemma lem4427082 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4427083 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term68 A K x k s) = (term69 A K x k t).
Proof. exact (MK_COMB (@lem4427082 A K x) (@lem4427081 A K k s t h1)). Qed.
Lemma lem4427085 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term33 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4426688 _83095 p x) (@lem4426687 _83095 p x)). Qed.
Lemma lem4427086 {A K : Type'} (p : type805 A K) (x : K -> A) : (term70 A K x p) = (p x).
Proof. exact (@lem4427085 (K -> A) p x). Qed.
Lemma lem4427087 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term71 A K x k t) = (term72 A K k t x).
Proof. exact (@lem4427086 A K (term73 A K k t) x). Qed.
Lemma lem4427088 {A K : Type'} (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term72 A K k t f) = (term62 A K k f t).
Proof. exact (eq_refl (term72 A K k t f)). Qed.
Lemma lem4427089 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4427090 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term74 A K GEN_PVAR_140 k t f) = (term63 A K GEN_PVAR_140 k f t).
Proof. exact (MK_COMB (@lem4427089 A K GEN_PVAR_140) (@lem4427088 A K k f t)). Qed.
Lemma lem4427091 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4427092 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) (f : K -> A) : (term75 A K GEN_PVAR_140 k t f) = (term64 A K GEN_PVAR_140 k t f).
Proof. exact (MK_COMB (@lem4427090 A K GEN_PVAR_140 k f t) (@lem4427091 A K f)). Qed.
Lemma lem4427093 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term76 A K GEN_PVAR_140 k t) = (term65 A K GEN_PVAR_140 k t).
Proof. exact (fun_ext (fun f : K -> A => @lem4427092 A K GEN_PVAR_140 k t f)). Qed.
Lemma lem4427094 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4427095 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term77 A K GEN_PVAR_140 k t) = (term66 A K GEN_PVAR_140 k t).
Proof. exact (MK_COMB (@lem4427094 A K) (@lem4427093 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4427096 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term78 A K k t) = (term67 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4427095 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4427097 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4427098 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term79 A K k t) = (term41 A K k t).
Proof. exact (MK_COMB (@lem4427097 A K) (@lem4427096 A K k t)). Qed.
Lemma lem4427099 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4427100 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term71 A K x k t) = (term69 A K x k t).
Proof. exact (MK_COMB (@lem4427099 A K x) (@lem4427098 A K k t)). Qed.
Lemma lem4427101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427102 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term80 A K x k t) = (term81 A K x k t).
Proof. exact (MK_COMB (@lem4427101) (@lem4427100 A K x k t)). Qed.
Lemma lem4427103 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term72 A K k t x) = (term62 A K k x t).
Proof. exact (eq_refl (term72 A K k t x)). Qed.
Lemma lem4427104 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term71 A K x k t) = (term72 A K k t x)) = ((term69 A K x k t) = (term62 A K k x t)).
Proof. exact (MK_COMB (@lem4427102 A K x k t) (@lem4427103 A K k x t)). Qed.
Lemma lem4427105 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term69 A K x k t) = (term62 A K k x t).
Proof. exact (EQ_MP (@lem4427104 A K k x t) (@lem4427087 A K k t x)). Qed.
Lemma lem4427135 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term68 A K x k s) = (term62 A K k x t).
Proof. exact (TRANS (@lem4427083 A K x k s t h1) (@lem4427105 A K k x t)). Qed.
Lemma lem4427136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427137 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term82 A K x k s) = (term83 A K k x t).
Proof. exact (MK_COMB (@lem4427136) (@lem4427135 A K x k s t h1)). Qed.
Lemma lem4427168 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term41 A K k s).
Proof. exact (EQ_MP (@lem4426707 A K k s) (@lem4426706 A K k s)). Qed.
Lemma lem4427169 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term41 A K k s).
Proof. exact (@lem4427168 A K k s). Qed.
Lemma lem4427170 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@cartesian_product A K k t) = (term41 A K k t).
Proof. exact (@lem4427169 A K k t). Qed.
Lemma lem4427204 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4427205 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term68 A K x k t) = (term69 A K x k t).
Proof. exact (MK_COMB (@lem4427204 A K x) (@lem4427170 A K k t)). Qed.
Lemma lem4427207 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term33 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4426688 _83095 p x) (@lem4426687 _83095 p x)). Qed.
Lemma lem4427208 {A K : Type'} (p : type805 A K) (x : K -> A) : (term70 A K x p) = (p x).
Proof. exact (@lem4427207 (K -> A) p x). Qed.
Lemma lem4427209 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term71 A K x k t) = (term72 A K k t x).
Proof. exact (@lem4427208 A K (term73 A K k t) x). Qed.
Lemma lem4427210 {A K : Type'} (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term72 A K k t f) = (term62 A K k f t).
Proof. exact (eq_refl (term72 A K k t f)). Qed.
Lemma lem4427211 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4427212 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (t : type1470 A K) : (term74 A K GEN_PVAR_140 k t f) = (term63 A K GEN_PVAR_140 k f t).
Proof. exact (MK_COMB (@lem4427211 A K GEN_PVAR_140) (@lem4427210 A K k f t)). Qed.
Lemma lem4427213 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4427214 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) (f : K -> A) : (term75 A K GEN_PVAR_140 k t f) = (term64 A K GEN_PVAR_140 k t f).
Proof. exact (MK_COMB (@lem4427212 A K GEN_PVAR_140 k f t) (@lem4427213 A K f)). Qed.
Lemma lem4427215 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term76 A K GEN_PVAR_140 k t) = (term65 A K GEN_PVAR_140 k t).
Proof. exact (fun_ext (fun f : K -> A => @lem4427214 A K GEN_PVAR_140 k t f)). Qed.
Lemma lem4427216 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4427217 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (t : type1470 A K) : (term77 A K GEN_PVAR_140 k t) = (term66 A K GEN_PVAR_140 k t).
Proof. exact (MK_COMB (@lem4427216 A K) (@lem4427215 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4427218 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term78 A K k t) = (term67 A K k t).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4427217 A K GEN_PVAR_140 k t)). Qed.
Lemma lem4427219 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4427220 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term79 A K k t) = (term41 A K k t).
Proof. exact (MK_COMB (@lem4427219 A K) (@lem4427218 A K k t)). Qed.
Lemma lem4427221 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4427222 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term71 A K x k t) = (term69 A K x k t).
Proof. exact (MK_COMB (@lem4427221 A K x) (@lem4427220 A K k t)). Qed.
Lemma lem4427223 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427224 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) : (term80 A K x k t) = (term81 A K x k t).
Proof. exact (MK_COMB (@lem4427223) (@lem4427222 A K x k t)). Qed.
Lemma lem4427225 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term72 A K k t x) = (term62 A K k x t).
Proof. exact (eq_refl (term72 A K k t x)). Qed.
Lemma lem4427226 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term71 A K x k t) = (term72 A K k t x)) = ((term69 A K x k t) = (term62 A K k x t)).
Proof. exact (MK_COMB (@lem4427224 A K x k t) (@lem4427225 A K k x t)). Qed.
Lemma lem4427227 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term69 A K x k t) = (term62 A K k x t).
Proof. exact (EQ_MP (@lem4427226 A K k x t) (@lem4427209 A K k t x)). Qed.
Lemma lem4427257 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : (term68 A K x k t) = (term62 A K k x t).
Proof. exact (TRANS (@lem4427205 A K x k t) (@lem4427227 A K k x t)). Qed.
Lemma lem4427258 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : ((term68 A K x k s) = (term68 A K x k t)) = ((term62 A K k x t) = (term62 A K k x t)).
Proof. exact (MK_COMB (@lem4427137 A K x k s t h1) (@lem4427257 A K k x t)). Qed.
Lemma lem4427260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4427261 (x : Prop) : (x = x) = True.
Proof. exact (@lem4427260 Prop x). Qed.
Lemma lem4427262 {A K : Type'} (k : K -> Prop) (x : K -> A) (t : type1470 A K) : ((term62 A K k x t) = (term62 A K k x t)) = True.
Proof. exact (@lem4427261 (term62 A K k x t)). Qed.
Lemma lem4427263 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : ((term68 A K x k s) = (term68 A K x k t)) = True.
Proof. exact (TRANS (@lem4427258 A K x k s t h1) (@lem4427262 A K k x t)). Qed.
Lemma lem4427264 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term84 A K s k t) = (term85 A K).
Proof. exact (fun_ext (fun x : K -> A => @lem4427263 A K x k s t h1)). Qed.
Lemma lem4427265 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4427266 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term43 A K s k t) = (term86 A K).
Proof. exact (MK_COMB (@lem4427265 A K) (@lem4427264 A K k s t h1)). Qed.
Lemma lem4427268 {A : Type'} (t : Prop) : (term21 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4427269 {A K : Type'} (t : Prop) : (term87 A K t) = t.
Proof. exact (@lem4427268 (K -> A) t). Qed.
Lemma lem4427270 {A K : Type'} : (term86 A K) = True.
Proof. exact (@lem4427269 A K True). Qed.
Lemma lem4427271 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (term43 A K s k t) = True.
Proof. exact (TRANS (@lem4427266 A K k s t h1) (@lem4427270 A K)). Qed.
Lemma lem4427272 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = True.
Proof. exact (TRANS (@lem4426724 A K s k t) (@lem4427271 A K k s t h1)). Qed.
Lemma lem4427273 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : True = ((@cartesian_product A K k s) = (@cartesian_product A K k t)).
Proof. exact (SYM (@lem4427272 A K k s t h1)). Qed.
Lemma lem4427274 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : (@cartesian_product A K k s) = (@cartesian_product A K k t).
Proof. exact (EQ_MP (@lem4427273 A K k s t h1) (@lem0)). Qed.
Lemma lem4427282 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (@cartesian_product A K k t) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4427283 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term88 A K k s) = (term88 A K k s).
Proof. exact (eq_refl (term88 A K k s)). Qed.
Lemma lem4427284 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = ((@cartesian_product A K k s) = (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4427283 A K k s) (@lem4427282 A K k t h1)). Qed.
Lemma lem4427287 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427288 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (term26 A K s k t) = (term89 A K k s).
Proof. exact (MK_COMB (@lem4427287) (@lem4427284 A K s k t h1)). Qed.
Lemma lem4427296 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (@cartesian_product A K k t) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4427297 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4427298 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (term88 A K k t) = (@eq ((K -> A) -> Prop) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4427297 A K) (@lem4427296 A K k t h1)). Qed.
Lemma lem4427299 {A K : Type'} : (@EMPTY (K -> A)) = (@EMPTY (K -> A)).
Proof. exact (eq_refl (@EMPTY (K -> A))). Qed.
Lemma lem4427300 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = ((@EMPTY (K -> A)) = (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4427298 A K k t h1) (@lem4427299 A K)). Qed.
Lemma lem4427302 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4427303 {A K : Type'} (x : type805 A K) : (x = x) = True.
Proof. exact (@lem4427302 (type805 A K) x). Qed.
Lemma lem4427304 {A K : Type'} : ((@EMPTY (K -> A)) = (@EMPTY (K -> A))) = True.
Proof. exact (@lem4427303 A K (@EMPTY (K -> A))). Qed.
Lemma lem4427305 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = True.
Proof. exact (TRANS (@lem4427300 A K k t h1) (@lem4427304 A K)). Qed.
Lemma lem4427306 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term90 A K k s) = (term90 A K k s).
Proof. exact (eq_refl (term90 A K k s)). Qed.
Lemma lem4427307 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (term25 A K s k t) = (term91 A K k s).
Proof. exact (MK_COMB (@lem4427306 A K k s) (@lem4427305 A K k t h1)). Qed.
Lemma lem4427309 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4427310 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term91 A K k s) = ((@cartesian_product A K k s) = (@EMPTY (K -> A))).
Proof. exact (@lem4427309 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427313 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (term25 A K s k t) = ((@cartesian_product A K k s) = (@EMPTY (K -> A))).
Proof. exact (TRANS (@lem4427307 A K s k t h1) (@lem4427310 A K k s)). Qed.
Lemma lem4427314 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)) = (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = ((@cartesian_product A K k s) = (@EMPTY (K -> A)))).
Proof. exact (MK_COMB (@lem4427288 A K s k t h1) (@lem4427313 A K s k t h1)). Qed.
Lemma lem4427316 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4427317 (x : Prop) : (x = x) = True.
Proof. exact (@lem4427316 Prop x). Qed.
Lemma lem4427318 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (((@cartesian_product A K k s) = (@EMPTY (K -> A))) = ((@cartesian_product A K k s) = (@EMPTY (K -> A)))) = True.
Proof. exact (@lem4427317 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427319 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)) = True.
Proof. exact (TRANS (@lem4427314 A K s k t h1) (@lem4427318 A K k s)). Qed.
Lemma lem4427320 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : True = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)).
Proof. exact (SYM (@lem4427319 A K s k t h1)). Qed.
Lemma lem4427321 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t).
Proof. exact (EQ_MP (@lem4427320 A K s k t h1) (@lem0)). Qed.
Lemma lem4427324 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term92 A K k t.
Proof. exact (@lem82 ((@cartesian_product A K k t) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427346 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4427324 A K k t (@lem4426572 A K k t h1)). Qed.
Lemma lem4427347 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term90 A K k s) = (term90 A K k s).
Proof. exact (eq_refl (term90 A K k s)). Qed.
Lemma lem4427348 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term25 A K s k t) = (term93 A K k s).
Proof. exact (MK_COMB (@lem4427347 A K k s) (@lem4427346 A K k t h1)). Qed.
Lemma lem4427350 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem4427351 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term93 A K k s) = False.
Proof. exact (@lem4427350 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427352 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term25 A K s k t) = False.
Proof. exact (TRANS (@lem4427348 A K s k t h1) (@lem4427351 A K k s)). Qed.
Lemma lem4427353 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (term26 A K s k t) = (term26 A K s k t).
Proof. exact (eq_refl (term26 A K s k t)). Qed.
Lemma lem4427354 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = False).
Proof. exact (MK_COMB (@lem4427353 A K s k t) (@lem4427352 A K s k t h1)). Qed.
Lemma lem4427356 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4427357 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = False) = (term94 A K s k t).
Proof. exact (@lem4427356 ((@cartesian_product A K k s) = (@cartesian_product A K k t))). Qed.
Lemma lem4427360 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)) = (term94 A K s k t).
Proof. exact (TRANS (@lem4427354 A K s k t h1) (@lem4427357 A K s k t)). Qed.
Lemma lem4427361 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term94 A K s k t) = (((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t)).
Proof. exact (SYM (@lem4427360 A K s k t h1)). Qed.
Lemma lem4427367 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (@cartesian_product A K k t) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4427368 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A))) : (@EMPTY (K -> A)) = (@cartesian_product A K k t).
Proof. exact (SYM (@lem4427367 A K k t h1)). Qed.
Lemma lem4427369 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@EMPTY (K -> A)) = (@cartesian_product A K k t)) : (@EMPTY (K -> A)) = (@cartesian_product A K k t).
Proof. exact (h1). Qed.
Lemma lem4427370 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : (@EMPTY (K -> A)) = (@cartesian_product A K k t)) : (@cartesian_product A K k t) = (@EMPTY (K -> A)).
Proof. exact (SYM (@lem4427369 A K k t h1)). Qed.
Lemma lem4427371 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = ((@EMPTY (K -> A)) = (@cartesian_product A K k t)).
Proof. exact (prop_ext (fun h1 : (@cartesian_product A K k t) = (@EMPTY (K -> A)) => @lem4427368 A K k t h1) (fun h1 : (@EMPTY (K -> A)) = (@cartesian_product A K k t) => @lem4427370 A K k t h1)). Qed.
Lemma lem4427372 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427373 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term11 A K k t) = (term95 A K k t).
Proof. exact (MK_COMB (@lem4427372) (@lem4427371 A K k t)). Qed.
Lemma lem4427374 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : term95 A K k t.
Proof. exact (EQ_MP (@lem4427373 A K k t) (@lem4426572 A K k t h1)). Qed.
Lemma lem4427375 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term96 A K k t.
Proof. exact (@lem82 ((@EMPTY (K -> A)) = (@cartesian_product A K k t))). Qed.
Lemma lem4427380 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (@cartesian_product A K k s) = (@EMPTY (K -> A)).
Proof. exact (h1). Qed.
Lemma lem4427381 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4427382 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term88 A K k s) = (@eq ((K -> A) -> Prop) (@EMPTY (K -> A))).
Proof. exact (MK_COMB (@lem4427381 A K) (@lem4427380 A K k s h1)). Qed.
Lemma lem4427383 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (@cartesian_product A K k t) = (@cartesian_product A K k t).
Proof. exact (eq_refl (@cartesian_product A K k t)). Qed.
Lemma lem4427384 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = ((@EMPTY (K -> A)) = (@cartesian_product A K k t)).
Proof. exact (MK_COMB (@lem4427382 A K k s h1) (@lem4427383 A K k t)). Qed.
Lemma lem4427386 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : ((@EMPTY (K -> A)) = (@cartesian_product A K k t)) = False.
Proof. exact (@lem4427375 A K k t (@lem4427374 A K k t h1)). Qed.
Lemma lem4427387 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k t) (h2 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = False.
Proof. exact (TRANS (@lem4427384 A K t k s h2) (@lem4427386 A K k t h1)). Qed.
Lemma lem4427388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427389 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k t) (h2 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term94 A K s k t) = (~ False).
Proof. exact (MK_COMB (@lem4427388) (@lem4427387 A K t k s h1 h2)). Qed.
Lemma lem4427391 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4427392 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k t) (h2 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : (term94 A K s k t) = True.
Proof. exact (TRANS (@lem4427389 A K t k s h1 h2) (@lem4427391)). Qed.
Lemma lem4427393 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k t) (h2 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : True = (term94 A K s k t).
Proof. exact (SYM (@lem4427392 A K t k s h1 h2)). Qed.
Lemma lem4427394 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k t) (h2 : (@cartesian_product A K k s) = (@EMPTY (K -> A))) : term94 A K s k t.
Proof. exact (EQ_MP (@lem4427393 A K t k s h1 h2) (@lem0)). Qed.
Lemma lem4427427 {A K : Type'} (k : K -> Prop) : term97 A K k.
Proof. exact (@lem4426548 A K k). Qed.
Lemma lem4427428 {A K : Type'} (k : K -> Prop) : (term97 A K k) = (term98 A K k).
Proof. exact (eq_refl (term97 A K k)). Qed.
Lemma lem4427429 {A K : Type'} (k : K -> Prop) : term98 A K k.
Proof. exact (EQ_MP (@lem4427428 A K k) (@lem4427427 A K k)). Qed.
Lemma lem4427430 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term99 A K k s.
Proof. exact (@lem4427429 A K k s). Qed.
Lemma lem4427431 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term99 A K k s) = (term100 A K k s).
Proof. exact (eq_refl (term99 A K k s)). Qed.
Lemma lem4427432 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term100 A K k s.
Proof. exact (EQ_MP (@lem4427431 A K k s) (@lem4427430 A K k s)). Qed.
Lemma lem4427433 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : term101 A K k s t.
Proof. exact (@lem4427432 A K k s t). Qed.
Lemma lem4427434 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term101 A K k s t) = ((term102 A K s k t) = (term103 A K k s t)).
Proof. exact (eq_refl (term101 A K k s t)). Qed.
Lemma lem4427436 {A : Type'} (s : A -> Prop) : term104 A s.
Proof. exact (@lem4426562 A s). Qed.
Lemma lem4427437 {A : Type'} (s : A -> Prop) : (term104 A s) = (term4 A s).
Proof. exact (eq_refl (term104 A s)). Qed.
Lemma lem4427438 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem4427437 A s) (@lem4427436 A s)). Qed.
Lemma lem4427439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term105 A s t.
Proof. exact (@lem4427438 A s t). Qed.
Lemma lem4427440 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term105 A s t) = ((s = t) = (term0 A t s)).
Proof. exact (eq_refl (term105 A s t)). Qed.
Lemma lem4427444 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : term92 A K k t.
Proof. exact (@lem82 ((@cartesian_product A K k t) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427457 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term92 A K k s.
Proof. exact (@lem82 ((@cartesian_product A K k s) = (@EMPTY (K -> A)))). Qed.
Lemma lem4427473 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (s = t) = (term0 A t s).
Proof. exact (EQ_MP (@lem4427440 A t s) (@lem4427439 A s t)). Qed.
Lemma lem4427474 {A K : Type'} (t : type805 A K) (s : type805 A K) : (s = t) = (term106 A K t s).
Proof. exact (@lem4427473 (K -> A) t s). Qed.
Lemma lem4427475 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term107 A K t k s).
Proof. exact (@lem4427474 A K (@cartesian_product A K k t) (@cartesian_product A K k s)). Qed.
Lemma lem4427479 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term102 A K s k t) = (term103 A K k s t).
Proof. exact (EQ_MP (@lem4427434 A K k s t) (@lem4427433 A K k s t)). Qed.
Lemma lem4427480 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term102 A K s k t) = (term103 A K k s t).
Proof. exact (@lem4427479 A K k s t). Qed.
Lemma lem4427484 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4427457 A K k s (@lem4426567 A K k s h1)). Qed.
Lemma lem4427485 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4427486 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : (term108 A K k s) = (or False).
Proof. exact (MK_COMB (@lem4427485) (@lem4427484 A K k s h1)). Qed.
Lemma lem4427493 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term109 A K k s t) = (term109 A K k s t).
Proof. exact (eq_refl (term109 A K k s t)). Qed.
Lemma lem4427494 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : (term103 A K k s t) = (term110 A K k s t).
Proof. exact (MK_COMB (@lem4427486 A K k s h1) (@lem4427493 A K k s t)). Qed.
Lemma lem4427496 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4427497 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term110 A K k s t) = (term109 A K k s t).
Proof. exact (@lem4427496 (term109 A K k s t)). Qed.
Lemma lem4427504 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : (term103 A K k s t) = (term109 A K k s t).
Proof. exact (TRANS (@lem4427494 A K t k s h1) (@lem4427497 A K k s t)). Qed.
Lemma lem4427505 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : (term102 A K s k t) = (term109 A K k s t).
Proof. exact (TRANS (@lem4427480 A K k s t) (@lem4427504 A K t k s h1)). Qed.
Lemma lem4427506 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427507 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (h1 : term11 A K k s) : (term111 A K s k t) = (term112 A K k s t).
Proof. exact (MK_COMB (@lem4427506) (@lem4427505 A K t k s h1)). Qed.
Lemma lem4427509 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term102 A K s k t) = (term103 A K k s t).
Proof. exact (EQ_MP (@lem4427434 A K k s t) (@lem4427433 A K k s t)). Qed.
Lemma lem4427510 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term102 A K s k t) = (term103 A K k s t).
Proof. exact (@lem4427509 A K k s t). Qed.
Lemma lem4427511 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term102 A K t k s) = (term103 A K k t s).
Proof. exact (@lem4427510 A K k t s). Qed.
Lemma lem4427515 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = False.
Proof. exact (@lem4427444 A K k t (@lem4426572 A K k t h1)). Qed.
Lemma lem4427516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4427517 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term108 A K k t) = (or False).
Proof. exact (MK_COMB (@lem4427516) (@lem4427515 A K k t h1)). Qed.
Lemma lem4427524 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term109 A K k t s) = (term109 A K k t s).
Proof. exact (eq_refl (term109 A K k t s)). Qed.
Lemma lem4427525 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term103 A K k t s) = (term110 A K k t s).
Proof. exact (MK_COMB (@lem4427517 A K k t h1) (@lem4427524 A K k t s)). Qed.
Lemma lem4427527 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem4427528 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term110 A K k t s) = (term109 A K k t s).
Proof. exact (@lem4427527 (term109 A K k t s)). Qed.
Lemma lem4427535 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term103 A K k t s) = (term109 A K k t s).
Proof. exact (TRANS (@lem4427525 A K s k t h1) (@lem4427528 A K k t s)). Qed.
Lemma lem4427536 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k t) : (term102 A K t k s) = (term109 A K k t s).
Proof. exact (TRANS (@lem4427511 A K k t s) (@lem4427535 A K s k t h1)). Qed.
Lemma lem4427537 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k s) (h2 : term11 A K k t) : (term107 A K t k s) = (term113 A K k t s).
Proof. exact (MK_COMB (@lem4427507 A K t k s h1) (@lem4427536 A K s k t h2)). Qed.
Lemma lem4427540 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k s) (h2 : term11 A K k t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term113 A K k t s).
Proof. exact (TRANS (@lem4427475 A K t k s) (@lem4427537 A K s k t h1 h2)). Qed.
Lemma lem4427541 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427542 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k s) (h2 : term11 A K k t) : (term94 A K s k t) = (term114 A K k t s).
Proof. exact (MK_COMB (@lem4427541) (@lem4427540 A K s k t h1 h2)). Qed.
Lemma lem4427543 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term11 A K k s) (h2 : term11 A K k t) : (term114 A K k t s) = (term94 A K s k t).
Proof. exact (SYM (@lem4427542 A K s k t h1 h2)). Qed.
Lemma lem4427554 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k t) : term115 A K k s t.
Proof. exact (conj (@lem4426572 A K k t h2) (@lem4426577 A K k s t h1)). Qed.
Lemma lem4427555 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k s) (h3 : term11 A K k t) : term116 A K k s t.
Proof. exact (conj (@lem4426567 A K k s h2) (@lem4427554 A K s k t h1 h3)). Qed.
Lemma lem4427563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4427564 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term42 A K s t).
Proof. exact (@lem4427563 (K -> A) s t). Qed.
Lemma lem4427565 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (@EMPTY (K -> A))) = (term117 A K k s).
Proof. exact (@lem4427564 A K (@cartesian_product A K k s) (@EMPTY (K -> A))). Qed.
Lemma lem4427574 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term11 A K k s) = (term118 A K k s).
Proof. exact (MK_COMB (@lem4427574) (@lem4427565 A K k s)). Qed.
Lemma lem4427576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427577 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term119 A K k s) = (term120 A K k s).
Proof. exact (MK_COMB (@lem4427576) (@lem4427575 A K k s)). Qed.
Lemma lem4427583 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4427584 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term42 A K s t).
Proof. exact (@lem4427583 (K -> A) s t). Qed.
Lemma lem4427585 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : ((@cartesian_product A K k t) = (@EMPTY (K -> A))) = (term117 A K k t).
Proof. exact (@lem4427584 A K (@cartesian_product A K k t) (@EMPTY (K -> A))). Qed.
Lemma lem4427594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427595 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term11 A K k t) = (term118 A K k t).
Proof. exact (MK_COMB (@lem4427594) (@lem4427585 A K k t)). Qed.
Lemma lem4427596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427597 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term119 A K k t) = (term120 A K k t).
Proof. exact (MK_COMB (@lem4427596) (@lem4427595 A K k t)). Qed.
Lemma lem4427607 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4427608 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (@lem4427607 A s t). Qed.
Lemma lem4427609 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((s i) = (t i)) = (term121 A K s t i).
Proof. exact (@lem4427608 A (s i) (t i)). Qed.
Lemma lem4427618 {K : Type'} (i : K) (k : K -> Prop) : (term122 K i k) = (term122 K i k).
Proof. exact (eq_refl (term122 K i k)). Qed.
Lemma lem4427619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term17 A K k s t i) = (term123 A K k s t i).
Proof. exact (MK_COMB (@lem4427618 K i k) (@lem4427609 A K s t i)). Qed.
Lemma lem4427622 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term18 A K k s t) = (term124 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4427619 A K k s t i)). Qed.
Lemma lem4427623 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term13 A K k s t) = (term125 A K k s t).
Proof. exact (MK_COMB (@lem4427623 K) (@lem4427622 A K k s t)). Qed.
Lemma lem4427629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427630 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term15 A K k s t) = (term126 A K k s t).
Proof. exact (MK_COMB (@lem4427629) (@lem4427624 A K k s t)). Qed.
Lemma lem4427631 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term115 A K k s t) = (term127 A K k s t).
Proof. exact (MK_COMB (@lem4427597 A K k t) (@lem4427630 A K k s t)). Qed.
Lemma lem4427634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term116 A K k s t) = (term128 A K k s t).
Proof. exact (MK_COMB (@lem4427577 A K k s) (@lem4427631 A K k s t)). Qed.
Lemma lem4427637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term129 A K k s t) = (term130 A K k s t).
Proof. exact (MK_COMB (@lem4427637) (@lem4427634 A K k s t)). Qed.
Lemma lem4427648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term131 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4427649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term131 A s t).
Proof. exact (@lem4427648 A s t). Qed.
Lemma lem4427650 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term132 A K s t i) = (term133 A K s t i).
Proof. exact (@lem4427649 A (s i) (t i)). Qed.
Lemma lem4427657 {K : Type'} (i : K) (k : K -> Prop) : (term122 K i k) = (term122 K i k).
Proof. exact (eq_refl (term122 K i k)). Qed.
Lemma lem4427658 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term134 A K k s t i) = (term135 A K k s t i).
Proof. exact (MK_COMB (@lem4427657 K i k) (@lem4427650 A K s t i)). Qed.
Lemma lem4427661 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term136 A K k s t) = (term137 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4427658 A K k s t i)). Qed.
Lemma lem4427662 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427663 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term109 A K k s t) = (term138 A K k s t).
Proof. exact (MK_COMB (@lem4427662 K) (@lem4427661 A K k s t)). Qed.
Lemma lem4427668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427669 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term112 A K k s t) = (term139 A K k s t).
Proof. exact (MK_COMB (@lem4427668) (@lem4427663 A K k s t)). Qed.
Lemma lem4427677 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term131 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4427678 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term131 A s t).
Proof. exact (@lem4427677 A s t). Qed.
Lemma lem4427679 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term132 A K t s i) = (term133 A K t s i).
Proof. exact (@lem4427678 A (t i) (s i)). Qed.
Lemma lem4427686 {K : Type'} (i : K) (k : K -> Prop) : (term122 K i k) = (term122 K i k).
Proof. exact (eq_refl (term122 K i k)). Qed.
Lemma lem4427687 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term134 A K k t s i) = (term135 A K k t s i).
Proof. exact (MK_COMB (@lem4427686 K i k) (@lem4427679 A K t s i)). Qed.
Lemma lem4427690 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term136 A K k t s) = (term137 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4427687 A K k t s i)). Qed.
Lemma lem4427691 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427692 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term109 A K k t s) = (term138 A K k t s).
Proof. exact (MK_COMB (@lem4427691 K) (@lem4427690 A K k t s)). Qed.
Lemma lem4427697 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term113 A K k t s) = (term140 A K k t s).
Proof. exact (MK_COMB (@lem4427669 A K k s t) (@lem4427692 A K k t s)). Qed.
Lemma lem4427700 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427701 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term114 A K k t s) = (term141 A K k t s).
Proof. exact (MK_COMB (@lem4427700) (@lem4427697 A K k t s)). Qed.
Lemma lem4427702 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term142 A K k t s) = (term143 A K k t s).
Proof. exact (MK_COMB (@lem4427638 A K k s t) (@lem4427701 A K k t s)). Qed.
Lemma lem4427705 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term143 A K k t s) = (term142 A K k t s).
Proof. exact (SYM (@lem4427702 A K k t s)). Qed.
Lemma lem4427717 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427718 {A K : Type'} (P : type805 A K) (x : K -> A) : (@IN (K -> A) x P) = (P x).
Proof. exact (@lem4427717 (K -> A) P x). Qed.
Lemma lem4427719 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term68 A K x k s) = (@cartesian_product A K k s x).
Proof. exact (@lem4427718 A K (@cartesian_product A K k s) x). Qed.
Lemma lem4427720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427721 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term82 A K x k s) = (term144 A K k s x).
Proof. exact (MK_COMB (@lem4427720) (@lem4427719 A K k s x)). Qed.
Lemma lem4427723 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4427724 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@EMPTY (K -> A))) = False.
Proof. exact (@lem4427723 (K -> A) x). Qed.
Lemma lem4427725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : ((term68 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))) = ((@cartesian_product A K k s x) = False).
Proof. exact (MK_COMB (@lem4427721 A K k s x) (@lem4427724 A K x)). Qed.
Lemma lem4427727 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4427728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : ((@cartesian_product A K k s x) = False) = (term145 A K k s x).
Proof. exact (@lem4427727 (@cartesian_product A K k s x)). Qed.
Lemma lem4427729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : ((term68 A K x k s) = (@IN (K -> A) x (@EMPTY (K -> A)))) = (term145 A K k s x).
Proof. exact (TRANS (@lem4427725 A K k s x) (@lem4427728 A K k s x)). Qed.
Lemma lem4427730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term146 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4427729 A K k s x)). Qed.
Lemma lem4427731 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4427732 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term117 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4427731 A K) (@lem4427730 A K k s)). Qed.
Lemma lem4427737 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427738 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term118 A K k s) = (term149 A K k s).
Proof. exact (MK_COMB (@lem4427737) (@lem4427732 A K k s)). Qed.
Lemma lem4427739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427740 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term120 A K k s) = (term150 A K k s).
Proof. exact (MK_COMB (@lem4427739) (@lem4427738 A K k s)). Qed.
Lemma lem4427750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427751 {A K : Type'} (P : type805 A K) (x : K -> A) : (@IN (K -> A) x P) = (P x).
Proof. exact (@lem4427750 (K -> A) P x). Qed.
Lemma lem4427752 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term68 A K x k t) = (@cartesian_product A K k t x).
Proof. exact (@lem4427751 A K (@cartesian_product A K k t) x). Qed.
Lemma lem4427753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427754 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term82 A K x k t) = (term144 A K k t x).
Proof. exact (MK_COMB (@lem4427753) (@lem4427752 A K k t x)). Qed.
Lemma lem4427756 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4427757 {A K : Type'} (x : K -> A) : (@IN (K -> A) x (@EMPTY (K -> A))) = False.
Proof. exact (@lem4427756 (K -> A) x). Qed.
Lemma lem4427758 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : ((term68 A K x k t) = (@IN (K -> A) x (@EMPTY (K -> A)))) = ((@cartesian_product A K k t x) = False).
Proof. exact (MK_COMB (@lem4427754 A K k t x) (@lem4427757 A K x)). Qed.
Lemma lem4427760 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4427761 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : ((@cartesian_product A K k t x) = False) = (term145 A K k t x).
Proof. exact (@lem4427760 (@cartesian_product A K k t x)). Qed.
Lemma lem4427762 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : ((term68 A K x k t) = (@IN (K -> A) x (@EMPTY (K -> A)))) = (term145 A K k t x).
Proof. exact (TRANS (@lem4427758 A K k t x) (@lem4427761 A K k t x)). Qed.
Lemma lem4427763 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term146 A K k t) = (term147 A K k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4427762 A K k t x)). Qed.
Lemma lem4427764 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4427765 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term117 A K k t) = (term148 A K k t).
Proof. exact (MK_COMB (@lem4427764 A K) (@lem4427763 A K k t)). Qed.
Lemma lem4427770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427771 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term118 A K k t) = (term149 A K k t).
Proof. exact (MK_COMB (@lem4427770) (@lem4427765 A K k t)). Qed.
Lemma lem4427772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427773 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term120 A K k t) = (term150 A K k t).
Proof. exact (MK_COMB (@lem4427772) (@lem4427771 A K k t)). Qed.
Lemma lem4427781 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427782 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4427781 K P x). Qed.
Lemma lem4427783 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4427782 K k i). Qed.
Lemma lem4427784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427785 {K : Type'} (k : K -> Prop) (i : K) : (term122 K i k) = (term151 K k i).
Proof. exact (MK_COMB (@lem4427784) (@lem4427783 K k i)). Qed.
Lemma lem4427793 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427794 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427793 A P x). Qed.
Lemma lem4427795 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K x s i) = (s i x).
Proof. exact (@lem4427794 A (s i) x). Qed.
Lemma lem4427796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4427797 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term153 A K x s i) = (term154 A K s i x).
Proof. exact (MK_COMB (@lem4427796) (@lem4427795 A K s i x)). Qed.
Lemma lem4427799 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427800 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427799 A P x). Qed.
Lemma lem4427801 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term152 A K x t i) = (t i x).
Proof. exact (@lem4427800 A (t i) x). Qed.
Lemma lem4427802 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : ((term152 A K x s i) = (term152 A K x t i)) = ((s i x) = (t i x)).
Proof. exact (MK_COMB (@lem4427797 A K s i x) (@lem4427801 A K t i x)). Qed.
Lemma lem4427805 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term155 A K s t i) = (term156 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4427802 A K s t i x)). Qed.
Lemma lem4427806 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4427807 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term121 A K s t i) = (term157 A K s t i).
Proof. exact (MK_COMB (@lem4427806 A) (@lem4427805 A K s t i)). Qed.
Lemma lem4427812 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term123 A K k s t i) = (term158 A K k s t i).
Proof. exact (MK_COMB (@lem4427785 K k i) (@lem4427807 A K s t i)). Qed.
Lemma lem4427815 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term124 A K k s t) = (term159 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4427812 A K k s t i)). Qed.
Lemma lem4427816 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427817 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term125 A K k s t) = (term160 A K k s t).
Proof. exact (MK_COMB (@lem4427816 K) (@lem4427815 A K k s t)). Qed.
Lemma lem4427822 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427823 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term126 A K k s t) = (term161 A K k s t).
Proof. exact (MK_COMB (@lem4427822) (@lem4427817 A K k s t)). Qed.
Lemma lem4427824 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term127 A K k s t) = (term162 A K k s t).
Proof. exact (MK_COMB (@lem4427773 A K k t) (@lem4427823 A K k s t)). Qed.
Lemma lem4427827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term128 A K k s t) = (term163 A K k s t).
Proof. exact (MK_COMB (@lem4427740 A K k s) (@lem4427824 A K k s t)). Qed.
Lemma lem4427830 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427831 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term130 A K k s t) = (term164 A K k s t).
Proof. exact (MK_COMB (@lem4427830) (@lem4427827 A K k s t)). Qed.
Lemma lem4427841 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427842 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4427841 K P x). Qed.
Lemma lem4427843 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4427842 K k i). Qed.
Lemma lem4427844 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427845 {K : Type'} (k : K -> Prop) (i : K) : (term122 K i k) = (term151 K k i).
Proof. exact (MK_COMB (@lem4427844) (@lem4427843 K k i)). Qed.
Lemma lem4427853 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427854 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427853 A P x). Qed.
Lemma lem4427855 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K x s i) = (s i x).
Proof. exact (@lem4427854 A (s i) x). Qed.
Lemma lem4427856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427857 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term165 A K x s i) = (term166 A K s i x).
Proof. exact (MK_COMB (@lem4427856) (@lem4427855 A K s i x)). Qed.
Lemma lem4427859 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427860 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427859 A P x). Qed.
Lemma lem4427861 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term152 A K x t i) = (t i x).
Proof. exact (@lem4427860 A (t i) x). Qed.
Lemma lem4427862 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term167 A K s x t i) = (term168 A K s t i x).
Proof. exact (MK_COMB (@lem4427857 A K s i x) (@lem4427861 A K t i x)). Qed.
Lemma lem4427865 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term169 A K s t i) = (term170 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4427862 A K s t i x)). Qed.
Lemma lem4427866 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4427867 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term133 A K s t i) = (term171 A K s t i).
Proof. exact (MK_COMB (@lem4427866 A) (@lem4427865 A K s t i)). Qed.
Lemma lem4427872 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term135 A K k s t i) = (term172 A K k s t i).
Proof. exact (MK_COMB (@lem4427845 K k i) (@lem4427867 A K s t i)). Qed.
Lemma lem4427875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term137 A K k s t) = (term173 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4427872 A K k s t i)). Qed.
Lemma lem4427876 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427877 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term138 A K k s t) = (term174 A K k s t).
Proof. exact (MK_COMB (@lem4427876 K) (@lem4427875 A K k s t)). Qed.
Lemma lem4427882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4427883 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term139 A K k s t) = (term175 A K k s t).
Proof. exact (MK_COMB (@lem4427882) (@lem4427877 A K k s t)). Qed.
Lemma lem4427891 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427892 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4427891 K P x). Qed.
Lemma lem4427893 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4427892 K k i). Qed.
Lemma lem4427894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427895 {K : Type'} (k : K -> Prop) (i : K) : (term122 K i k) = (term151 K k i).
Proof. exact (MK_COMB (@lem4427894) (@lem4427893 K k i)). Qed.
Lemma lem4427903 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427904 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427903 A P x). Qed.
Lemma lem4427905 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term152 A K x t i) = (t i x).
Proof. exact (@lem4427904 A (t i) x). Qed.
Lemma lem4427906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4427907 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term165 A K x t i) = (term166 A K t i x).
Proof. exact (MK_COMB (@lem4427906) (@lem4427905 A K t i x)). Qed.
Lemma lem4427909 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4427910 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4427909 A P x). Qed.
Lemma lem4427911 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term152 A K x s i) = (s i x).
Proof. exact (@lem4427910 A (s i) x). Qed.
Lemma lem4427912 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term167 A K t x s i) = (term168 A K t s i x).
Proof. exact (MK_COMB (@lem4427907 A K t i x) (@lem4427911 A K s i x)). Qed.
Lemma lem4427915 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term169 A K t s i) = (term170 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4427912 A K t s i x)). Qed.
Lemma lem4427916 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4427917 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term133 A K t s i) = (term171 A K t s i).
Proof. exact (MK_COMB (@lem4427916 A) (@lem4427915 A K t s i)). Qed.
Lemma lem4427922 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term135 A K k t s i) = (term172 A K k t s i).
Proof. exact (MK_COMB (@lem4427895 K k i) (@lem4427917 A K t s i)). Qed.
Lemma lem4427925 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term137 A K k t s) = (term173 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4427922 A K k t s i)). Qed.
Lemma lem4427926 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4427927 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term138 A K k t s) = (term174 A K k t s).
Proof. exact (MK_COMB (@lem4427926 K) (@lem4427925 A K k t s)). Qed.
Lemma lem4427932 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term140 A K k t s) = (term176 A K k t s).
Proof. exact (MK_COMB (@lem4427883 A K k s t) (@lem4427927 A K k t s)). Qed.
Lemma lem4427935 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4427936 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term141 A K k t s) = (term177 A K k t s).
Proof. exact (MK_COMB (@lem4427935) (@lem4427932 A K k t s)). Qed.
Lemma lem4427937 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term143 A K k t s) = (term178 A K k t s).
Proof. exact (MK_COMB (@lem4427831 A K k s t) (@lem4427936 A K k t s)). Qed.
Lemma lem4427940 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term178 A K k t s) = (term143 A K k t s).
Proof. exact (SYM (@lem4427937 A K k t s)). Qed.
Lemma lem4427942 (p : Prop) : p = (term179 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4427943 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term178 A K k t s) = (term180 A K k t s).
Proof. exact (@lem4427942 (term178 A K k t s)). Qed.
Lemma lem4427944 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term180 A K k t s) = (term178 A K k t s).
Proof. exact (SYM (@lem4427943 A K k t s)). Qed.
Lemma lem4427945 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term181 A K k t s) : term181 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4427948 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term180 A K k t s) : term180 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4427949 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term182 A K k t s.
Proof. exact (fun h0 : term180 A K k t s => @lem4427948 A K k t s h0). Qed.
Lemma lem4427950 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term182 A K k t s) : term182 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4427951 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term180 A K k t s) : term180 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4427952 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term180 A K k t s) (h2 : term182 A K k t s) : term180 A K k t s.
Proof. exact (@lem4427950 A K k t s h2 (@lem4427951 A K k t s h1)). Qed.
Lemma lem4427953 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term180 A K k t s) : term183 A K k t s.
Proof. exact (fun h0 : term182 A K k t s => @lem4427952 A K k t s h1 h0). Qed.
Lemma lem4427954 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term182 A K k t s) : term182 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4427955 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term180 A K k t s) (h2 : term182 A K k t s) : term180 A K k t s.
Proof. exact (@lem4427953 A K k t s h1 (@lem4427954 A K k t s h2)). Qed.
Lemma lem4427956 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term182 A K k t s) : term182 A K k t s.
Proof. exact (fun h0 : term180 A K k t s => @lem4427955 A K k t s h0 h1). Qed.
Lemma lem4427957 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term184 A K k t s.
Proof. exact (fun h0 : term182 A K k t s => @lem4427956 A K k t s h0). Qed.
Lemma lem4427960 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term182 A K k t s.
Proof. exact (@lem4427957 A K k t s (@lem4427949 A K k t s)). Qed.
Lemma lem4427961 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term182 A K k t s.
Proof. exact (@lem4427960 A K k t s). Qed.
Lemma lem4427975 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4427976 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term180 A K k t s) = (term185 A K k t s).
Proof. exact (@lem4427975 (term181 A K k t s)). Qed.
Lemma lem4427978 (t : Prop) : (term186 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4427979 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term185 A K k t s) = (term178 A K k t s).
Proof. exact (@lem4427978 (term178 A K k t s)). Qed.
Lemma lem4427982 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term180 A K k t s) = (term178 A K k t s).
Proof. exact (TRANS (@lem4427976 A K k t s) (@lem4427979 A K k t s)). Qed.
Lemma lem4428031 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : (term187 A K t s) = (term188 A K t s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4427982 A K k t s)). Qed.
Lemma lem4428032 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4428033 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : (term189 A K t s) = (term190 A K t s).
Proof. exact (MK_COMB (@lem4428032 K) (@lem4428031 A K t s)). Qed.
Lemma lem4428038 {A K : Type'} (s : type1470 A K) : (term191 A K s) = (term192 A K s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4428033 A K t s)). Qed.
Lemma lem4428039 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4428040 {A K : Type'} (s : type1470 A K) : (term193 A K s) = (term194 A K s).
Proof. exact (MK_COMB (@lem4428039 A K) (@lem4428038 A K s)). Qed.
Lemma lem4428045 {A K : Type'} : (term195 A K) = (term196 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4428040 A K s)). Qed.
Lemma lem4428046 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4428055 {A K : Type'} : (term197 A K) = (term198 A K).
Proof. exact (MK_COMB (@lem4428046 A K) (@lem4428045 A K)). Qed.
Lemma lem4428060 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term168 A K t s i x) = (term168 A K t s i x).
Proof. exact (eq_refl (term168 A K t s i x)). Qed.
Lemma lem4428061 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term170 A K t s i) = (term170 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4428060 A K t s i x)). Qed.
Lemma lem4428062 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4428063 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term171 A K t s i) = (term171 A K t s i).
Proof. exact (MK_COMB (@lem4428062 A) (@lem4428061 A K t s i)). Qed.
Lemma lem4428066 {K : Type'} (k : K -> Prop) (i : K) : (term151 K k i) = (term151 K k i).
Proof. exact (eq_refl (term151 K k i)). Qed.
Lemma lem4428067 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term172 A K k t s i) = (term172 A K k t s i).
Proof. exact (MK_COMB (@lem4428066 K k i) (@lem4428063 A K t s i)). Qed.
Lemma lem4428068 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term173 A K k t s) = (term173 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4428067 A K k t s i)). Qed.
Lemma lem4428069 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4428070 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term174 A K k t s) = (term174 A K k t s).
Proof. exact (MK_COMB (@lem4428069 K) (@lem4428068 A K k t s)). Qed.
Lemma lem4428075 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term168 A K s t i x) = (term168 A K s t i x).
Proof. exact (eq_refl (term168 A K s t i x)). Qed.
Lemma lem4428076 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term170 A K s t i) = (term170 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428075 A K s t i x)). Qed.
Lemma lem4428077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4428078 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term171 A K s t i) = (term171 A K s t i).
Proof. exact (MK_COMB (@lem4428077 A) (@lem4428076 A K s t i)). Qed.
Lemma lem4428081 {K : Type'} (k : K -> Prop) (i : K) : (term151 K k i) = (term151 K k i).
Proof. exact (eq_refl (term151 K k i)). Qed.
Lemma lem4428082 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term172 A K k s t i) = (term172 A K k s t i).
Proof. exact (MK_COMB (@lem4428081 K k i) (@lem4428078 A K s t i)). Qed.
Lemma lem4428083 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term173 A K k s t) = (term173 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428082 A K k s t i)). Qed.
Lemma lem4428084 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4428085 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term174 A K k s t) = (term174 A K k s t).
Proof. exact (MK_COMB (@lem4428084 K) (@lem4428083 A K k s t)). Qed.
Lemma lem4428086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428087 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term175 A K k s t) = (term175 A K k s t).
Proof. exact (MK_COMB (@lem4428086) (@lem4428085 A K k s t)). Qed.
Lemma lem4428088 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term176 A K k t s) = (term176 A K k t s).
Proof. exact (MK_COMB (@lem4428087 A K k s t) (@lem4428070 A K k t s)). Qed.
Lemma lem4428089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428090 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term177 A K k t s) = (term177 A K k t s).
Proof. exact (MK_COMB (@lem4428089) (@lem4428088 A K k t s)). Qed.
Lemma lem4428095 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : ((s i x) = (t i x)) = ((s i x) = (t i x)).
Proof. exact (eq_refl ((s i x) = (t i x))). Qed.
Lemma lem4428096 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term156 A K s t i) = (term156 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428095 A K s t i x)). Qed.
Lemma lem4428097 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4428098 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term157 A K s t i) = (term157 A K s t i).
Proof. exact (MK_COMB (@lem4428097 A) (@lem4428096 A K s t i)). Qed.
Lemma lem4428101 {K : Type'} (k : K -> Prop) (i : K) : (term151 K k i) = (term151 K k i).
Proof. exact (eq_refl (term151 K k i)). Qed.
Lemma lem4428102 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term158 A K k s t i) = (term158 A K k s t i).
Proof. exact (MK_COMB (@lem4428101 K k i) (@lem4428098 A K s t i)). Qed.
Lemma lem4428103 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term159 A K k s t) = (term159 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428102 A K k s t i)). Qed.
Lemma lem4428104 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4428105 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term160 A K k s t) = (term160 A K k s t).
Proof. exact (MK_COMB (@lem4428104 K) (@lem4428103 A K k s t)). Qed.
Lemma lem4428106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428107 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term161 A K k s t) = (term161 A K k s t).
Proof. exact (MK_COMB (@lem4428106) (@lem4428105 A K k s t)). Qed.
Lemma lem4428110 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term145 A K k t x) = (term145 A K k t x).
Proof. exact (eq_refl (term145 A K k t x)). Qed.
Lemma lem4428111 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term147 A K k t) = (term147 A K k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428110 A K k t x)). Qed.
Lemma lem4428112 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4428113 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term148 A K k t) = (term148 A K k t).
Proof. exact (MK_COMB (@lem4428112 A K) (@lem4428111 A K k t)). Qed.
Lemma lem4428114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428115 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term149 A K k t) = (term149 A K k t).
Proof. exact (MK_COMB (@lem4428114) (@lem4428113 A K k t)). Qed.
Lemma lem4428116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428117 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term150 A K k t) = (term150 A K k t).
Proof. exact (MK_COMB (@lem4428116) (@lem4428115 A K k t)). Qed.
Lemma lem4428118 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term162 A K k s t) = (term162 A K k s t).
Proof. exact (MK_COMB (@lem4428117 A K k t) (@lem4428107 A K k s t)). Qed.
Lemma lem4428121 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term145 A K k s x) = (term145 A K k s x).
Proof. exact (eq_refl (term145 A K k s x)). Qed.
Lemma lem4428122 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term147 A K k s) = (term147 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4428121 A K k s x)). Qed.
Lemma lem4428123 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4428124 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term148 A K k s) = (term148 A K k s).
Proof. exact (MK_COMB (@lem4428123 A K) (@lem4428122 A K k s)). Qed.
Lemma lem4428125 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428126 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term149 A K k s) = (term149 A K k s).
Proof. exact (MK_COMB (@lem4428125) (@lem4428124 A K k s)). Qed.
Lemma lem4428127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428128 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term150 A K k s) = (term150 A K k s).
Proof. exact (MK_COMB (@lem4428127) (@lem4428126 A K k s)). Qed.
Lemma lem4428129 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term163 A K k s t) = (term163 A K k s t).
Proof. exact (MK_COMB (@lem4428128 A K k s) (@lem4428118 A K k s t)). Qed.
Lemma lem4428130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4428131 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term164 A K k s t) = (term164 A K k s t).
Proof. exact (MK_COMB (@lem4428130) (@lem4428129 A K k s t)). Qed.
Lemma lem4428132 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term178 A K k t s) = (term178 A K k t s).
Proof. exact (MK_COMB (@lem4428131 A K k s t) (@lem4428090 A K k t s)). Qed.
Lemma lem4428133 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : (term188 A K t s) = (term188 A K t s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4428132 A K k t s)). Qed.
Lemma lem4428134 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4428135 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : (term190 A K t s) = (term190 A K t s).
Proof. exact (MK_COMB (@lem4428134 K) (@lem4428133 A K t s)). Qed.
Lemma lem4428136 {A K : Type'} (s : type1470 A K) : (term192 A K s) = (term192 A K s).
Proof. exact (fun_ext (fun t : type1470 A K => @lem4428135 A K t s)). Qed.
Lemma lem4428137 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4428138 {A K : Type'} (s : type1470 A K) : (term194 A K s) = (term194 A K s).
Proof. exact (MK_COMB (@lem4428137 A K) (@lem4428136 A K s)). Qed.
Lemma lem4428139 {A K : Type'} : (term196 A K) = (term196 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4428138 A K s)). Qed.
Lemma lem4428140 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4428141 {A K : Type'} : (term198 A K) = (term198 A K).
Proof. exact (MK_COMB (@lem4428140 A K) (@lem4428139 A K)). Qed.
Lemma lem4428228 {A K : Type'} : (term197 A K) = (term198 A K).
Proof. exact (TRANS (@lem4428055 A K) (@lem4428141 A K)). Qed.
Lemma lem4428229 {A K : Type'} : (term198 A K) = (term197 A K).
Proof. exact (SYM (@lem4428228 A K)). Qed.
Lemma lem4428230 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term163 A K k s t) : term163 A K k s t.
Proof. exact (h1). Qed.
Lemma lem4428231 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term176 A K k t s.
Proof. exact (h1). Qed.
Lemma lem4428234 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term199 A K k s x) = (@cartesian_product A K k s x).
Proof. exact (@lem16933 (@cartesian_product A K k s x)). Qed.
Lemma lem4428235 {A K : Type'} (P : type805 A K) : (term200 A K P) = (term201 A K P).
Proof. exact (@lem18392 (K -> A) P). Qed.
Lemma lem4428236 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term149 A K k s) = (term202 A K k s).
Proof. exact (@lem4428235 A K (term147 A K k s)). Qed.
Lemma lem4428237 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term203 A K k s x) = (term145 A K k s x).
Proof. exact (eq_refl (term203 A K k s x)). Qed.
Lemma lem4428238 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428239 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term204 A K k s x) = (term199 A K k s x).
Proof. exact (MK_COMB (@lem4428238) (@lem4428237 A K k s x)). Qed.
Lemma lem4428240 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term204 A K k s x) = (@cartesian_product A K k s x).
Proof. exact (TRANS (@lem4428239 A K k s x) (@lem4428234 A K k s x)). Qed.
Lemma lem4428241 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term205 A K k s) = (term206 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4428240 A K k s x)). Qed.
Lemma lem4428242 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428243 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term202 A K k s) = (term207 A K k s).
Proof. exact (MK_COMB (@lem4428242 A K) (@lem4428241 A K k s)). Qed.
Lemma lem4428244 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term149 A K k s) = (term207 A K k s).
Proof. exact (TRANS (@lem4428236 A K k s) (@lem4428243 A K k s)). Qed.
Lemma lem4428247 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term199 A K k t x) = (@cartesian_product A K k t x).
Proof. exact (@lem16933 (@cartesian_product A K k t x)). Qed.
Lemma lem4428248 {A K : Type'} (P : type805 A K) : (term200 A K P) = (term201 A K P).
Proof. exact (@lem18392 (K -> A) P). Qed.
Lemma lem4428249 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term149 A K k t) = (term202 A K k t).
Proof. exact (@lem4428248 A K (term147 A K k t)). Qed.
Lemma lem4428250 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term203 A K k t x) = (term145 A K k t x).
Proof. exact (eq_refl (term203 A K k t x)). Qed.
Lemma lem4428251 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428252 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term204 A K k t x) = (term199 A K k t x).
Proof. exact (MK_COMB (@lem4428251) (@lem4428250 A K k t x)). Qed.
Lemma lem4428253 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term204 A K k t x) = (@cartesian_product A K k t x).
Proof. exact (TRANS (@lem4428252 A K k t x) (@lem4428247 A K k t x)). Qed.
Lemma lem4428254 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term205 A K k t) = (term206 A K k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428253 A K k t x)). Qed.
Lemma lem4428255 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428256 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term202 A K k t) = (term207 A K k t).
Proof. exact (MK_COMB (@lem4428255 A K) (@lem4428254 A K k t)). Qed.
Lemma lem4428257 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term149 A K k t) = (term207 A K k t).
Proof. exact (TRANS (@lem4428249 A K k t) (@lem4428256 A K k t)). Qed.
Lemma lem4428273 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term208 A K s t i x) = (term209 A K s t i x).
Proof. exact (@lem17646 (s i x) (t i x)). Qed.
Lemma lem4428274 {A : Type'} (P : A -> Prop) : (term210 A P) = (term211 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4428275 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term212 A K s t i) = (term213 A K s t i).
Proof. exact (@lem4428274 A (term156 A K s t i)). Qed.
Lemma lem4428276 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term214 A K s t i x) = ((s i x) = (t i x)).
Proof. exact (eq_refl (term214 A K s t i x)). Qed.
Lemma lem4428277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428278 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term215 A K s t i x) = (term208 A K s t i x).
Proof. exact (MK_COMB (@lem4428277) (@lem4428276 A K s t i x)). Qed.
Lemma lem4428279 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term215 A K s t i x) = (term209 A K s t i x).
Proof. exact (TRANS (@lem4428278 A K s t i x) (@lem4428273 A K s t i x)). Qed.
Lemma lem4428280 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term216 A K s t i) = (term217 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428279 A K s t i x)). Qed.
Lemma lem4428281 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428282 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term213 A K s t i) = (term218 A K s t i).
Proof. exact (MK_COMB (@lem4428281 A) (@lem4428280 A K s t i)). Qed.
Lemma lem4428283 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term212 A K s t i) = (term218 A K s t i).
Proof. exact (TRANS (@lem4428275 A K s t i) (@lem4428282 A K s t i)). Qed.
Lemma lem4428285 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term219 K k i).
Proof. exact (eq_refl (term219 K k i)). Qed.
Lemma lem4428286 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term220 A K k s t i) = (term221 A K k s t i).
Proof. exact (MK_COMB (@lem4428285 K k i) (@lem4428283 A K s t i)). Qed.
Lemma lem4428287 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term222 A K k s t i) = (term220 A K k s t i).
Proof. exact (@lem17362 (k i) (term157 A K s t i)). Qed.
Lemma lem4428288 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term222 A K k s t i) = (term221 A K k s t i).
Proof. exact (TRANS (@lem4428287 A K k s t i) (@lem4428286 A K k s t i)). Qed.
Lemma lem4428289 {K : Type'} (P : K -> Prop) : (term210 K P) = (term211 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4428290 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term161 A K k s t) = (term223 A K k s t).
Proof. exact (@lem4428289 K (term159 A K k s t)). Qed.
Lemma lem4428291 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term224 A K k s t i) = (term158 A K k s t i).
Proof. exact (eq_refl (term224 A K k s t i)). Qed.
Lemma lem4428292 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428293 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term225 A K k s t i) = (term222 A K k s t i).
Proof. exact (MK_COMB (@lem4428292) (@lem4428291 A K k s t i)). Qed.
Lemma lem4428294 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term225 A K k s t i) = (term221 A K k s t i).
Proof. exact (TRANS (@lem4428293 A K k s t i) (@lem4428288 A K k s t i)). Qed.
Lemma lem4428295 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term226 A K k s t) = (term227 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428294 A K k s t i)). Qed.
Lemma lem4428296 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428297 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term223 A K k s t) = (term228 A K k s t).
Proof. exact (MK_COMB (@lem4428296 K) (@lem4428295 A K k s t)). Qed.
Lemma lem4428298 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term161 A K k s t) = (term228 A K k s t).
Proof. exact (TRANS (@lem4428290 A K k s t) (@lem4428297 A K k s t)). Qed.
Lemma lem4428299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428300 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term150 A K k t) = (term229 A K k t).
Proof. exact (MK_COMB (@lem4428299) (@lem4428257 A K k t)). Qed.
Lemma lem4428301 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term162 A K k s t) = (term230 A K k s t).
Proof. exact (MK_COMB (@lem4428300 A K k t) (@lem4428298 A K k s t)). Qed.
Lemma lem4428302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428303 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term150 A K k s) = (term229 A K k s).
Proof. exact (MK_COMB (@lem4428302) (@lem4428244 A K k s)). Qed.
Lemma lem4428304 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term163 A K k s t) = (term231 A K k s t).
Proof. exact (MK_COMB (@lem4428303 A K k s) (@lem4428301 A K k s t)). Qed.
Lemma lem4428342 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4428343 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term232 A P Q) = (term233 A P Q).
Proof. exact (@lem4428342 A P Q). Qed.
Lemma lem4428344 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term234 A K s t i) = (term235 A K s t i).
Proof. exact (@lem4428343 A (term236 A K s t i) (term237 A K s t i)). Qed.
Lemma lem4428345 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term238 A K s t i x) = (term239 A K s t i x).
Proof. exact (eq_refl (term238 A K s t i x)). Qed.
Lemma lem4428346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4428347 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term240 A K s t i x) = (term241 A K s t i x).
Proof. exact (MK_COMB (@lem4428346) (@lem4428345 A K s t i x)). Qed.
Lemma lem4428348 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term242 A K s t i x) = (term243 A K s t i x).
Proof. exact (eq_refl (term242 A K s t i x)). Qed.
Lemma lem4428349 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term244 A K s t i x) = (term209 A K s t i x).
Proof. exact (MK_COMB (@lem4428347 A K s t i x) (@lem4428348 A K s t i x)). Qed.
Lemma lem4428350 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term245 A K s t i) = (term217 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428349 A K s t i x)). Qed.
Lemma lem4428351 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428352 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term234 A K s t i) = (term218 A K s t i).
Proof. exact (MK_COMB (@lem4428351 A) (@lem4428350 A K s t i)). Qed.
Lemma lem4428353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428354 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term246 A K s t i) = (term247 A K s t i).
Proof. exact (MK_COMB (@lem4428353) (@lem4428352 A K s t i)). Qed.
Lemma lem4428355 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term238 A K s t i x) = (term239 A K s t i x).
Proof. exact (eq_refl (term238 A K s t i x)). Qed.
Lemma lem4428356 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term248 A K s t i) = (term236 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428355 A K s t i x)). Qed.
Lemma lem4428357 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428358 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term249 A K s t i) = (term250 A K s t i).
Proof. exact (MK_COMB (@lem4428357 A) (@lem4428356 A K s t i)). Qed.
Lemma lem4428359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4428360 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K s t i) = (term252 A K s t i).
Proof. exact (MK_COMB (@lem4428359) (@lem4428358 A K s t i)). Qed.
Lemma lem4428361 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term242 A K s t i x) = (term243 A K s t i x).
Proof. exact (eq_refl (term242 A K s t i x)). Qed.
Lemma lem4428362 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term253 A K s t i) = (term237 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428361 A K s t i x)). Qed.
Lemma lem4428363 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428364 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term254 A K s t i) = (term255 A K s t i).
Proof. exact (MK_COMB (@lem4428363 A) (@lem4428362 A K s t i)). Qed.
Lemma lem4428365 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term235 A K s t i) = (term256 A K s t i).
Proof. exact (MK_COMB (@lem4428360 A K s t i) (@lem4428364 A K s t i)). Qed.
Lemma lem4428366 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term234 A K s t i) = (term235 A K s t i)) = ((term218 A K s t i) = (term256 A K s t i)).
Proof. exact (MK_COMB (@lem4428354 A K s t i) (@lem4428365 A K s t i)). Qed.
Lemma lem4428367 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term218 A K s t i) = (term256 A K s t i).
Proof. exact (EQ_MP (@lem4428366 A K s t i) (@lem4428344 A K s t i)). Qed.
Lemma lem4428464 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term219 K k i).
Proof. exact (eq_refl (term219 K k i)). Qed.
Lemma lem4428465 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term221 A K k s t i) = (term257 A K k s t i).
Proof. exact (MK_COMB (@lem4428464 K k i) (@lem4428367 A K s t i)). Qed.
Lemma lem4428466 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term227 A K k s t) = (term258 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428465 A K k s t i)). Qed.
Lemma lem4428467 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428468 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term228 A K k s t) = (term259 A K k s t).
Proof. exact (MK_COMB (@lem4428467 K) (@lem4428466 A K k s t)). Qed.
Lemma lem4428497 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term229 A K k t) = (term229 A K k t).
Proof. exact (eq_refl (term229 A K k t)). Qed.
Lemma lem4428498 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term230 A K k s t) = (term260 A K k s t).
Proof. exact (MK_COMB (@lem4428497 A K k t) (@lem4428468 A K k s t)). Qed.
Lemma lem4428499 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term229 A K k s) = (term229 A K k s).
Proof. exact (eq_refl (term229 A K k s)). Qed.
Lemma lem4428500 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term231 A K k s t) = (term261 A K k s t).
Proof. exact (MK_COMB (@lem4428499 A K k s) (@lem4428498 A K k s t)). Qed.
Lemma lem4428502 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4428503 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term233 A P Q) = (term232 A P Q).
Proof. exact (@lem4428502 A P Q). Qed.
Lemma lem4428504 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term235 A K s t i) = (term234 A K s t i).
Proof. exact (@lem4428503 A (term236 A K s t i) (term237 A K s t i)). Qed.
Lemma lem4428505 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term238 A K s t i x) = (term239 A K s t i x).
Proof. exact (eq_refl (term238 A K s t i x)). Qed.
Lemma lem4428506 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term248 A K s t i) = (term236 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428505 A K s t i x)). Qed.
Lemma lem4428507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428508 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term249 A K s t i) = (term250 A K s t i).
Proof. exact (MK_COMB (@lem4428507 A) (@lem4428506 A K s t i)). Qed.
Lemma lem4428509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4428510 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term251 A K s t i) = (term252 A K s t i).
Proof. exact (MK_COMB (@lem4428509) (@lem4428508 A K s t i)). Qed.
Lemma lem4428511 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term242 A K s t i x) = (term243 A K s t i x).
Proof. exact (eq_refl (term242 A K s t i x)). Qed.
Lemma lem4428512 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term253 A K s t i) = (term237 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428511 A K s t i x)). Qed.
Lemma lem4428513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428514 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term254 A K s t i) = (term255 A K s t i).
Proof. exact (MK_COMB (@lem4428513 A) (@lem4428512 A K s t i)). Qed.
Lemma lem4428515 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term235 A K s t i) = (term256 A K s t i).
Proof. exact (MK_COMB (@lem4428510 A K s t i) (@lem4428514 A K s t i)). Qed.
Lemma lem4428516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428517 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term262 A K s t i) = (term263 A K s t i).
Proof. exact (MK_COMB (@lem4428516) (@lem4428515 A K s t i)). Qed.
Lemma lem4428518 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term238 A K s t i x) = (term239 A K s t i x).
Proof. exact (eq_refl (term238 A K s t i x)). Qed.
Lemma lem4428519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4428520 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term240 A K s t i x) = (term241 A K s t i x).
Proof. exact (MK_COMB (@lem4428519) (@lem4428518 A K s t i x)). Qed.
Lemma lem4428521 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term242 A K s t i x) = (term243 A K s t i x).
Proof. exact (eq_refl (term242 A K s t i x)). Qed.
Lemma lem4428522 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term244 A K s t i x) = (term209 A K s t i x).
Proof. exact (MK_COMB (@lem4428520 A K s t i x) (@lem4428521 A K s t i x)). Qed.
Lemma lem4428523 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term245 A K s t i) = (term217 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428522 A K s t i x)). Qed.
Lemma lem4428524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428525 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term234 A K s t i) = (term218 A K s t i).
Proof. exact (MK_COMB (@lem4428524 A) (@lem4428523 A K s t i)). Qed.
Lemma lem4428526 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : ((term235 A K s t i) = (term234 A K s t i)) = ((term256 A K s t i) = (term218 A K s t i)).
Proof. exact (MK_COMB (@lem4428517 A K s t i) (@lem4428525 A K s t i)). Qed.
Lemma lem4428527 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term256 A K s t i) = (term218 A K s t i).
Proof. exact (EQ_MP (@lem4428526 A K s t i) (@lem4428504 A K s t i)). Qed.
Lemma lem4428528 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term219 K k i).
Proof. exact (eq_refl (term219 K k i)). Qed.
Lemma lem4428529 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term257 A K k s t i) = (term221 A K k s t i).
Proof. exact (MK_COMB (@lem4428528 K k i) (@lem4428527 A K s t i)). Qed.
Lemma lem4428531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428532 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (@lem4428531 A P Q). Qed.
Lemma lem4428533 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term266 A K k s t i) = (term267 A K k s t i).
Proof. exact (@lem4428532 A (k i) (term217 A K s t i)). Qed.
Lemma lem4428534 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term268 A K s t i x) = (term209 A K s t i x).
Proof. exact (eq_refl (term268 A K s t i x)). Qed.
Lemma lem4428535 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term269 A K s t i) = (term217 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428534 A K s t i x)). Qed.
Lemma lem4428536 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428537 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term270 A K s t i) = (term218 A K s t i).
Proof. exact (MK_COMB (@lem4428536 A) (@lem4428535 A K s t i)). Qed.
Lemma lem4428538 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term219 K k i).
Proof. exact (eq_refl (term219 K k i)). Qed.
Lemma lem4428539 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term266 A K k s t i) = (term221 A K k s t i).
Proof. exact (MK_COMB (@lem4428538 K k i) (@lem4428537 A K s t i)). Qed.
Lemma lem4428540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428541 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term271 A K k s t i) = (term272 A K k s t i).
Proof. exact (MK_COMB (@lem4428540) (@lem4428539 A K k s t i)). Qed.
Lemma lem4428542 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term268 A K s t i x) = (term209 A K s t i x).
Proof. exact (eq_refl (term268 A K s t i x)). Qed.
Lemma lem4428543 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term219 K k i).
Proof. exact (eq_refl (term219 K k i)). Qed.
Lemma lem4428544 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term273 A K k s t i x) = (term274 A K k s t i x).
Proof. exact (MK_COMB (@lem4428543 K k i) (@lem4428542 A K s t i x)). Qed.
Lemma lem4428545 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term275 A K k s t i) = (term276 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4428544 A K k s t i x)). Qed.
Lemma lem4428546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428547 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term267 A K k s t i) = (term277 A K k s t i).
Proof. exact (MK_COMB (@lem4428546 A) (@lem4428545 A K k s t i)). Qed.
Lemma lem4428548 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term266 A K k s t i) = (term267 A K k s t i)) = ((term221 A K k s t i) = (term277 A K k s t i)).
Proof. exact (MK_COMB (@lem4428541 A K k s t i) (@lem4428547 A K k s t i)). Qed.
Lemma lem4428549 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term221 A K k s t i) = (term277 A K k s t i).
Proof. exact (EQ_MP (@lem4428548 A K k s t i) (@lem4428533 A K k s t i)). Qed.
Lemma lem4428550 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term257 A K k s t i) = (term277 A K k s t i).
Proof. exact (TRANS (@lem4428529 A K k s t i) (@lem4428549 A K k s t i)). Qed.
Lemma lem4428551 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term258 A K k s t) = (term278 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428550 A K k s t i)). Qed.
Lemma lem4428552 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428553 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term259 A K k s t) = (term279 A K k s t).
Proof. exact (MK_COMB (@lem4428552 K) (@lem4428551 A K k s t)). Qed.
Lemma lem4428554 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term229 A K k t) = (term229 A K k t).
Proof. exact (eq_refl (term229 A K k t)). Qed.
Lemma lem4428555 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term260 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4428554 A K k t) (@lem4428553 A K k s t)). Qed.
Lemma lem4428557 {A : Type'} (P : A -> Prop) (Q : Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4428558 {A K : Type'} (P : type805 A K) (Q : Prop) : (term283 A K P Q) = (term284 A K P Q).
Proof. exact (@lem4428557 (K -> A) P Q). Qed.
Lemma lem4428559 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term286 A K k s t).
Proof. exact (@lem4428558 A K (term206 A K k t) (term279 A K k s t)). Qed.
Lemma lem4428560 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term287 A K k t x) = (@cartesian_product A K k t x).
Proof. exact (eq_refl (term287 A K k t x)). Qed.
Lemma lem4428561 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term288 A K k t) = (term206 A K k t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428560 A K k t x)). Qed.
Lemma lem4428562 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428563 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term289 A K k t) = (term207 A K k t).
Proof. exact (MK_COMB (@lem4428562 A K) (@lem4428561 A K k t)). Qed.
Lemma lem4428564 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428565 {A K : Type'} (k : K -> Prop) (t : type1470 A K) : (term290 A K k t) = (term229 A K k t).
Proof. exact (MK_COMB (@lem4428564) (@lem4428563 A K k t)). Qed.
Lemma lem4428566 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term279 A K k s t) = (term279 A K k s t).
Proof. exact (eq_refl (term279 A K k s t)). Qed.
Lemma lem4428567 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term285 A K k s t) = (term280 A K k s t).
Proof. exact (MK_COMB (@lem4428565 A K k t) (@lem4428566 A K k s t)). Qed.
Lemma lem4428568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428569 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term291 A K k s t) = (term292 A K k s t).
Proof. exact (MK_COMB (@lem4428568) (@lem4428567 A K k s t)). Qed.
Lemma lem4428570 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term287 A K k t x) = (@cartesian_product A K k t x).
Proof. exact (eq_refl (term287 A K k t x)). Qed.
Lemma lem4428571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428572 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term293 A K k t x) = (term294 A K k t x).
Proof. exact (MK_COMB (@lem4428571) (@lem4428570 A K k t x)). Qed.
Lemma lem4428573 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term279 A K k s t) = (term279 A K k s t).
Proof. exact (eq_refl (term279 A K k s t)). Qed.
Lemma lem4428574 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term295 A K x k s t) = (term296 A K x k s t).
Proof. exact (MK_COMB (@lem4428572 A K k t x) (@lem4428573 A K k s t)). Qed.
Lemma lem4428575 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term297 A K k s t) = (term298 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428574 A K x k s t)). Qed.
Lemma lem4428576 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428577 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term286 A K k s t) = (term299 A K k s t).
Proof. exact (MK_COMB (@lem4428576 A K) (@lem4428575 A K k s t)). Qed.
Lemma lem4428578 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term285 A K k s t) = (term286 A K k s t)) = ((term280 A K k s t) = (term299 A K k s t)).
Proof. exact (MK_COMB (@lem4428569 A K k s t) (@lem4428577 A K k s t)). Qed.
Lemma lem4428579 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term299 A K k s t).
Proof. exact (EQ_MP (@lem4428578 A K k s t) (@lem4428559 A K k s t)). Qed.
Lemma lem4428581 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428582 {K : Type'} (P : Prop) (Q : K -> Prop) : (term264 K P Q) = (term265 K P Q).
Proof. exact (@lem4428581 K P Q). Qed.
Lemma lem4428583 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term300 A K x k s t) = (term301 A K x k s t).
Proof. exact (@lem4428582 K (@cartesian_product A K k t x) (term278 A K k s t)). Qed.
Lemma lem4428584 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term302 A K k s t i) = (term277 A K k s t i).
Proof. exact (eq_refl (term302 A K k s t i)). Qed.
Lemma lem4428585 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term303 A K k s t) = (term278 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428584 A K k s t i)). Qed.
Lemma lem4428586 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428587 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term304 A K k s t) = (term279 A K k s t).
Proof. exact (MK_COMB (@lem4428586 K) (@lem4428585 A K k s t)). Qed.
Lemma lem4428588 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term294 A K k t x) = (term294 A K k t x).
Proof. exact (eq_refl (term294 A K k t x)). Qed.
Lemma lem4428589 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term300 A K x k s t) = (term296 A K x k s t).
Proof. exact (MK_COMB (@lem4428588 A K k t x) (@lem4428587 A K k s t)). Qed.
Lemma lem4428590 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428591 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term305 A K x k s t) = (term306 A K x k s t).
Proof. exact (MK_COMB (@lem4428590) (@lem4428589 A K x k s t)). Qed.
Lemma lem4428592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term302 A K k s t i) = (term277 A K k s t i).
Proof. exact (eq_refl (term302 A K k s t i)). Qed.
Lemma lem4428593 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term294 A K k t x) = (term294 A K k t x).
Proof. exact (eq_refl (term294 A K k t x)). Qed.
Lemma lem4428594 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term307 A K x k s t i) = (term308 A K x k s t i).
Proof. exact (MK_COMB (@lem4428593 A K k t x) (@lem4428592 A K k s t i)). Qed.
Lemma lem4428595 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term309 A K x k s t) = (term310 A K x k s t).
Proof. exact (fun_ext (fun i : K => @lem4428594 A K x k s t i)). Qed.
Lemma lem4428596 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428597 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term301 A K x k s t) = (term311 A K x k s t).
Proof. exact (MK_COMB (@lem4428596 K) (@lem4428595 A K x k s t)). Qed.
Lemma lem4428598 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term300 A K x k s t) = (term301 A K x k s t)) = ((term296 A K x k s t) = (term311 A K x k s t)).
Proof. exact (MK_COMB (@lem4428591 A K x k s t) (@lem4428597 A K x k s t)). Qed.
Lemma lem4428599 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term296 A K x k s t) = (term311 A K x k s t).
Proof. exact (EQ_MP (@lem4428598 A K x k s t) (@lem4428583 A K x k s t)). Qed.
Lemma lem4428601 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428602 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (@lem4428601 A P Q). Qed.
Lemma lem4428603 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term312 A K x k s t i) = (term313 A K x k s t i).
Proof. exact (@lem4428602 A (@cartesian_product A K k t x) (term276 A K k s t i)). Qed.
Lemma lem4428604 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term314 A K k s t i x) = (term274 A K k s t i x).
Proof. exact (eq_refl (term314 A K k s t i x)). Qed.
Lemma lem4428605 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term315 A K k s t i) = (term276 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4428604 A K k s t i x)). Qed.
Lemma lem4428606 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428607 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term316 A K k s t i) = (term277 A K k s t i).
Proof. exact (MK_COMB (@lem4428606 A) (@lem4428605 A K k s t i)). Qed.
Lemma lem4428608 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term294 A K k t x) = (term294 A K k t x).
Proof. exact (eq_refl (term294 A K k t x)). Qed.
Lemma lem4428609 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term312 A K x k s t i) = (term308 A K x k s t i).
Proof. exact (MK_COMB (@lem4428608 A K k t x) (@lem4428607 A K k s t i)). Qed.
Lemma lem4428610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428611 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term317 A K x k s t i) = (term318 A K x k s t i).
Proof. exact (MK_COMB (@lem4428610) (@lem4428609 A K x k s t i)). Qed.
Lemma lem4428612 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term314 A K k s t i x) = (term274 A K k s t i x).
Proof. exact (eq_refl (term314 A K k s t i x)). Qed.
Lemma lem4428613 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x : K -> A) : (term294 A K k t x) = (term294 A K k t x).
Proof. exact (eq_refl (term294 A K k t x)). Qed.
Lemma lem4428614 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x' : A) : (term319 A K x k s t i x') = (term320 A K x k s t i x').
Proof. exact (MK_COMB (@lem4428613 A K k t x) (@lem4428612 A K k s t i x')). Qed.
Lemma lem4428615 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term321 A K x k s t i) = (term322 A K x k s t i).
Proof. exact (fun_ext (fun x' : A => @lem4428614 A K x k s t i x')). Qed.
Lemma lem4428616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428617 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term313 A K x k s t i) = (term323 A K x k s t i).
Proof. exact (MK_COMB (@lem4428616 A) (@lem4428615 A K x k s t i)). Qed.
Lemma lem4428618 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term312 A K x k s t i) = (term313 A K x k s t i)) = ((term308 A K x k s t i) = (term323 A K x k s t i)).
Proof. exact (MK_COMB (@lem4428611 A K x k s t i) (@lem4428617 A K x k s t i)). Qed.
Lemma lem4428619 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term308 A K x k s t i) = (term323 A K x k s t i).
Proof. exact (EQ_MP (@lem4428618 A K x k s t i) (@lem4428603 A K x k s t i)). Qed.
Lemma lem4428620 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term310 A K x k s t) = (term324 A K x k s t).
Proof. exact (fun_ext (fun i : K => @lem4428619 A K x k s t i)). Qed.
Lemma lem4428621 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428622 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term311 A K x k s t) = (term325 A K x k s t).
Proof. exact (MK_COMB (@lem4428621 K) (@lem4428620 A K x k s t)). Qed.
Lemma lem4428623 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term296 A K x k s t) = (term325 A K x k s t).
Proof. exact (TRANS (@lem4428599 A K x k s t) (@lem4428622 A K x k s t)). Qed.
Lemma lem4428624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term298 A K k s t) = (term326 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428623 A K x k s t)). Qed.
Lemma lem4428625 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428626 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term299 A K k s t) = (term327 A K k s t).
Proof. exact (MK_COMB (@lem4428625 A K) (@lem4428624 A K k s t)). Qed.
Lemma lem4428627 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term280 A K k s t) = (term327 A K k s t).
Proof. exact (TRANS (@lem4428579 A K k s t) (@lem4428626 A K k s t)). Qed.
Lemma lem4428628 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term260 A K k s t) = (term327 A K k s t).
Proof. exact (TRANS (@lem4428555 A K k s t) (@lem4428627 A K k s t)). Qed.
Lemma lem4428629 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term229 A K k s) = (term229 A K k s).
Proof. exact (eq_refl (term229 A K k s)). Qed.
Lemma lem4428630 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term261 A K k s t) = (term328 A K k s t).
Proof. exact (MK_COMB (@lem4428629 A K k s) (@lem4428628 A K k s t)). Qed.
Lemma lem4428632 {A : Type'} (P : A -> Prop) (Q : Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4428633 {A K : Type'} (P : type805 A K) (Q : Prop) : (term283 A K P Q) = (term284 A K P Q).
Proof. exact (@lem4428632 (K -> A) P Q). Qed.
Lemma lem4428634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term329 A K k s t) = (term330 A K k s t).
Proof. exact (@lem4428633 A K (term206 A K k s) (term327 A K k s t)). Qed.
Lemma lem4428635 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term287 A K k s x) = (@cartesian_product A K k s x).
Proof. exact (eq_refl (term287 A K k s x)). Qed.
Lemma lem4428636 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term288 A K k s) = (term206 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4428635 A K k s x)). Qed.
Lemma lem4428637 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428638 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term289 A K k s) = (term207 A K k s).
Proof. exact (MK_COMB (@lem4428637 A K) (@lem4428636 A K k s)). Qed.
Lemma lem4428639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428640 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term290 A K k s) = (term229 A K k s).
Proof. exact (MK_COMB (@lem4428639) (@lem4428638 A K k s)). Qed.
Lemma lem4428641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term327 A K k s t) = (term327 A K k s t).
Proof. exact (eq_refl (term327 A K k s t)). Qed.
Lemma lem4428642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term329 A K k s t) = (term328 A K k s t).
Proof. exact (MK_COMB (@lem4428640 A K k s) (@lem4428641 A K k s t)). Qed.
Lemma lem4428643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term331 A K k s t) = (term332 A K k s t).
Proof. exact (MK_COMB (@lem4428643) (@lem4428642 A K k s t)). Qed.
Lemma lem4428645 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term287 A K k s x) = (@cartesian_product A K k s x).
Proof. exact (eq_refl (term287 A K k s x)). Qed.
Lemma lem4428646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428647 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term293 A K k s x) = (term294 A K k s x).
Proof. exact (MK_COMB (@lem4428646) (@lem4428645 A K k s x)). Qed.
Lemma lem4428648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term327 A K k s t) = (term327 A K k s t).
Proof. exact (eq_refl (term327 A K k s t)). Qed.
Lemma lem4428649 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term333 A K x k s t) = (term334 A K x k s t).
Proof. exact (MK_COMB (@lem4428647 A K k s x) (@lem4428648 A K k s t)). Qed.
Lemma lem4428650 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term335 A K k s t) = (term336 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428649 A K x k s t)). Qed.
Lemma lem4428651 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428652 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term330 A K k s t) = (term337 A K k s t).
Proof. exact (MK_COMB (@lem4428651 A K) (@lem4428650 A K k s t)). Qed.
Lemma lem4428653 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term329 A K k s t) = (term330 A K k s t)) = ((term328 A K k s t) = (term337 A K k s t)).
Proof. exact (MK_COMB (@lem4428644 A K k s t) (@lem4428652 A K k s t)). Qed.
Lemma lem4428654 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term328 A K k s t) = (term337 A K k s t).
Proof. exact (EQ_MP (@lem4428653 A K k s t) (@lem4428634 A K k s t)). Qed.
Lemma lem4428656 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428657 {A K : Type'} (P : Prop) (Q : type805 A K) : (term338 A K P Q) = (term339 A K P Q).
Proof. exact (@lem4428656 (K -> A) P Q). Qed.
Lemma lem4428658 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term340 A K x k s t) = (term341 A K x k s t).
Proof. exact (@lem4428657 A K (@cartesian_product A K k s x) (term326 A K k s t)). Qed.
Lemma lem4428659 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term342 A K k s t x) = (term325 A K x k s t).
Proof. exact (eq_refl (term342 A K k s t x)). Qed.
Lemma lem4428660 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term343 A K k s t) = (term326 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428659 A K x k s t)). Qed.
Lemma lem4428661 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428662 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term344 A K k s t) = (term327 A K k s t).
Proof. exact (MK_COMB (@lem4428661 A K) (@lem4428660 A K k s t)). Qed.
Lemma lem4428663 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428664 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term340 A K x k s t) = (term334 A K x k s t).
Proof. exact (MK_COMB (@lem4428663 A K k s x) (@lem4428662 A K k s t)). Qed.
Lemma lem4428665 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428666 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term345 A K x k s t) = (term346 A K x k s t).
Proof. exact (MK_COMB (@lem4428665) (@lem4428664 A K x k s t)). Qed.
Lemma lem4428667 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term342 A K k s t x') = (term325 A K x' k s t).
Proof. exact (eq_refl (term342 A K k s t x')). Qed.
Lemma lem4428668 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428669 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term347 A K x k s t x') = (term348 A K x x' k s t).
Proof. exact (MK_COMB (@lem4428668 A K k s x) (@lem4428667 A K x' k s t)). Qed.
Lemma lem4428670 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term349 A K x k s t) = (term350 A K x k s t).
Proof. exact (fun_ext (fun x' : K -> A => @lem4428669 A K x x' k s t)). Qed.
Lemma lem4428671 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428672 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term341 A K x k s t) = (term351 A K x k s t).
Proof. exact (MK_COMB (@lem4428671 A K) (@lem4428670 A K x k s t)). Qed.
Lemma lem4428673 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term340 A K x k s t) = (term341 A K x k s t)) = ((term334 A K x k s t) = (term351 A K x k s t)).
Proof. exact (MK_COMB (@lem4428666 A K x k s t) (@lem4428672 A K x k s t)). Qed.
Lemma lem4428674 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term334 A K x k s t) = (term351 A K x k s t).
Proof. exact (EQ_MP (@lem4428673 A K x k s t) (@lem4428658 A K x k s t)). Qed.
Lemma lem4428676 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428677 {K : Type'} (P : Prop) (Q : K -> Prop) : (term264 K P Q) = (term265 K P Q).
Proof. exact (@lem4428676 K P Q). Qed.
Lemma lem4428678 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term352 A K x x' k s t) = (term353 A K x x' k s t).
Proof. exact (@lem4428677 K (@cartesian_product A K k s x) (term324 A K x' k s t)). Qed.
Lemma lem4428679 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term354 A K x' k s t i) = (term323 A K x' k s t i).
Proof. exact (eq_refl (term354 A K x' k s t i)). Qed.
Lemma lem4428680 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term355 A K x' k s t) = (term324 A K x' k s t).
Proof. exact (fun_ext (fun i : K => @lem4428679 A K x' k s t i)). Qed.
Lemma lem4428681 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428682 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term356 A K x' k s t) = (term325 A K x' k s t).
Proof. exact (MK_COMB (@lem4428681 K) (@lem4428680 A K x' k s t)). Qed.
Lemma lem4428683 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428684 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term352 A K x x' k s t) = (term348 A K x x' k s t).
Proof. exact (MK_COMB (@lem4428683 A K k s x) (@lem4428682 A K x' k s t)). Qed.
Lemma lem4428685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428686 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term357 A K x x' k s t) = (term358 A K x x' k s t).
Proof. exact (MK_COMB (@lem4428685) (@lem4428684 A K x x' k s t)). Qed.
Lemma lem4428687 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term354 A K x' k s t i) = (term323 A K x' k s t i).
Proof. exact (eq_refl (term354 A K x' k s t i)). Qed.
Lemma lem4428688 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428689 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term359 A K x x' k s t i) = (term360 A K x x' k s t i).
Proof. exact (MK_COMB (@lem4428688 A K k s x) (@lem4428687 A K x' k s t i)). Qed.
Lemma lem4428690 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term361 A K x x' k s t) = (term362 A K x x' k s t).
Proof. exact (fun_ext (fun i : K => @lem4428689 A K x x' k s t i)). Qed.
Lemma lem4428691 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428692 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term353 A K x x' k s t) = (term363 A K x x' k s t).
Proof. exact (MK_COMB (@lem4428691 K) (@lem4428690 A K x x' k s t)). Qed.
Lemma lem4428693 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((term352 A K x x' k s t) = (term353 A K x x' k s t)) = ((term348 A K x x' k s t) = (term363 A K x x' k s t)).
Proof. exact (MK_COMB (@lem4428686 A K x x' k s t) (@lem4428692 A K x x' k s t)). Qed.
Lemma lem4428694 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term348 A K x x' k s t) = (term363 A K x x' k s t).
Proof. exact (EQ_MP (@lem4428693 A K x x' k s t) (@lem4428678 A K x x' k s t)). Qed.
Lemma lem4428696 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4428697 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (@lem4428696 A P Q). Qed.
Lemma lem4428698 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term364 A K x x' k s t i) = (term365 A K x x' k s t i).
Proof. exact (@lem4428697 A (@cartesian_product A K k s x) (term322 A K x' k s t i)). Qed.
Lemma lem4428699 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term366 A K x' k s t i x) = (term320 A K x' k s t i x).
Proof. exact (eq_refl (term366 A K x' k s t i x)). Qed.
Lemma lem4428700 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term367 A K x' k s t i) = (term322 A K x' k s t i).
Proof. exact (fun_ext (fun x : A => @lem4428699 A K x' k s t i x)). Qed.
Lemma lem4428701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428702 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term368 A K x' k s t i) = (term323 A K x' k s t i).
Proof. exact (MK_COMB (@lem4428701 A) (@lem4428700 A K x' k s t i)). Qed.
Lemma lem4428703 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428704 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term364 A K x x' k s t i) = (term360 A K x x' k s t i).
Proof. exact (MK_COMB (@lem4428703 A K k s x) (@lem4428702 A K x' k s t i)). Qed.
Lemma lem4428705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4428706 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term369 A K x x' k s t i) = (term370 A K x x' k s t i).
Proof. exact (MK_COMB (@lem4428705) (@lem4428704 A K x x' k s t i)). Qed.
Lemma lem4428707 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term366 A K x' k s t i x) = (term320 A K x' k s t i x).
Proof. exact (eq_refl (term366 A K x' k s t i x)). Qed.
Lemma lem4428708 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4428709 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term371 A K x x' k s t i x'') = (term372 A K x x' k s t i x'').
Proof. exact (MK_COMB (@lem4428708 A K k s x) (@lem4428707 A K x' k s t i x'')). Qed.
Lemma lem4428710 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term373 A K x x' k s t i) = (term374 A K x x' k s t i).
Proof. exact (fun_ext (fun x'' : A => @lem4428709 A K x x' k s t i x'')). Qed.
Lemma lem4428711 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4428712 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term365 A K x x' k s t i) = (term375 A K x x' k s t i).
Proof. exact (MK_COMB (@lem4428711 A) (@lem4428710 A K x x' k s t i)). Qed.
Lemma lem4428713 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term364 A K x x' k s t i) = (term365 A K x x' k s t i)) = ((term360 A K x x' k s t i) = (term375 A K x x' k s t i)).
Proof. exact (MK_COMB (@lem4428706 A K x x' k s t i) (@lem4428712 A K x x' k s t i)). Qed.
Lemma lem4428714 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term360 A K x x' k s t i) = (term375 A K x x' k s t i).
Proof. exact (EQ_MP (@lem4428713 A K x x' k s t i) (@lem4428698 A K x x' k s t i)). Qed.
Lemma lem4428715 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term362 A K x x' k s t) = (term376 A K x x' k s t).
Proof. exact (fun_ext (fun i : K => @lem4428714 A K x x' k s t i)). Qed.
Lemma lem4428716 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4428717 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term363 A K x x' k s t) = (term377 A K x x' k s t).
Proof. exact (MK_COMB (@lem4428716 K) (@lem4428715 A K x x' k s t)). Qed.
Lemma lem4428718 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term348 A K x x' k s t) = (term377 A K x x' k s t).
Proof. exact (TRANS (@lem4428694 A K x x' k s t) (@lem4428717 A K x x' k s t)). Qed.
Lemma lem4428719 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term350 A K x k s t) = (term378 A K x k s t).
Proof. exact (fun_ext (fun x' : K -> A => @lem4428718 A K x x' k s t)). Qed.
Lemma lem4428720 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428721 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term351 A K x k s t) = (term379 A K x k s t).
Proof. exact (MK_COMB (@lem4428720 A K) (@lem4428719 A K x k s t)). Qed.
Lemma lem4428722 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term334 A K x k s t) = (term379 A K x k s t).
Proof. exact (TRANS (@lem4428674 A K x k s t) (@lem4428721 A K x k s t)). Qed.
Lemma lem4428723 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term336 A K k s t) = (term380 A K k s t).
Proof. exact (fun_ext (fun x : K -> A => @lem4428722 A K x k s t)). Qed.
Lemma lem4428724 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4428725 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term337 A K k s t) = (term381 A K k s t).
Proof. exact (MK_COMB (@lem4428724 A K) (@lem4428723 A K k s t)). Qed.
Lemma lem4428726 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term328 A K k s t) = (term381 A K k s t).
Proof. exact (TRANS (@lem4428654 A K k s t) (@lem4428725 A K k s t)). Qed.
Lemma lem4428727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term261 A K k s t) = (term381 A K k s t).
Proof. exact (TRANS (@lem4428630 A K k s t) (@lem4428726 A K k s t)). Qed.
Lemma lem4428728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term231 A K k s t) = (term381 A K k s t).
Proof. exact (TRANS (@lem4428500 A K k s t) (@lem4428727 A K k s t)). Qed.
Lemma lem4428729 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term163 A K k s t) = (term381 A K k s t).
Proof. exact (TRANS (@lem4428304 A K k s t) (@lem4428728 A K k s t)). Qed.
Lemma lem4428730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term163 A K k s t) : term381 A K k s t.
Proof. exact (EQ_MP (@lem4428729 A K k s t) (@lem4428230 A K k s t h1)). Qed.
Lemma lem4428738 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term168 A K s t i x) = (term382 A K s t i x).
Proof. exact (@lem17265 (s i x) (t i x)). Qed.
Lemma lem4428739 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term170 A K s t i) = (term383 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4428738 A K s t i x)). Qed.
Lemma lem4428740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4428741 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term171 A K s t i) = (term384 A K s t i).
Proof. exact (MK_COMB (@lem4428740 A) (@lem4428739 A K s t i)). Qed.
Lemma lem4428743 {K : Type'} (k : K -> Prop) (i : K) : (term385 K k i) = (term385 K k i).
Proof. exact (eq_refl (term385 K k i)). Qed.
Lemma lem4428744 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term386 A K k s t i) = (term387 A K k s t i).
Proof. exact (MK_COMB (@lem4428743 K k i) (@lem4428741 A K s t i)). Qed.
Lemma lem4428745 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term172 A K k s t i) = (term386 A K k s t i).
Proof. exact (@lem17265 (k i) (term171 A K s t i)). Qed.
Lemma lem4428746 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term172 A K k s t i) = (term387 A K k s t i).
Proof. exact (TRANS (@lem4428745 A K k s t i) (@lem4428744 A K k s t i)). Qed.
Lemma lem4428747 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term173 A K k s t) = (term388 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4428746 A K k s t i)). Qed.
Lemma lem4428748 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4428749 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term174 A K k s t) = (term389 A K k s t).
Proof. exact (MK_COMB (@lem4428748 K) (@lem4428747 A K k s t)). Qed.
Lemma lem4428757 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term168 A K t s i x) = (term382 A K t s i x).
Proof. exact (@lem17265 (t i x) (s i x)). Qed.
Lemma lem4428758 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term170 A K t s i) = (term383 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4428757 A K t s i x)). Qed.
Lemma lem4428759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4428760 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term171 A K t s i) = (term384 A K t s i).
Proof. exact (MK_COMB (@lem4428759 A) (@lem4428758 A K t s i)). Qed.
Lemma lem4428762 {K : Type'} (k : K -> Prop) (i : K) : (term385 K k i) = (term385 K k i).
Proof. exact (eq_refl (term385 K k i)). Qed.
Lemma lem4428763 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term386 A K k t s i) = (term387 A K k t s i).
Proof. exact (MK_COMB (@lem4428762 K k i) (@lem4428760 A K t s i)). Qed.
Lemma lem4428764 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term172 A K k t s i) = (term386 A K k t s i).
Proof. exact (@lem17265 (k i) (term171 A K t s i)). Qed.
Lemma lem4428765 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term172 A K k t s i) = (term387 A K k t s i).
Proof. exact (TRANS (@lem4428764 A K k t s i) (@lem4428763 A K k t s i)). Qed.
Lemma lem4428766 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term173 A K k t s) = (term388 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4428765 A K k t s i)). Qed.
Lemma lem4428767 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4428768 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term174 A K k t s) = (term389 A K k t s).
Proof. exact (MK_COMB (@lem4428767 K) (@lem4428766 A K k t s)). Qed.
Lemma lem4428769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4428770 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term175 A K k s t) = (term390 A K k s t).
Proof. exact (MK_COMB (@lem4428769) (@lem4428749 A K k s t)). Qed.
Lemma lem4428967 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term176 A K k t s) = (term391 A K k t s).
Proof. exact (MK_COMB (@lem4428770 A K k s t) (@lem4428768 A K k t s)). Qed.
Lemma lem4428968 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term391 A K k t s.
Proof. exact (EQ_MP (@lem4428967 A K k t s) (@lem4428231 A K k t s h1)). Qed.
Lemma lem4428969 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term379 A K x k s t) : term379 A K x k s t.
Proof. exact (h1). Qed.
Lemma lem4428970 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term377 A K x x' k s t) : term377 A K x x' k s t.
Proof. exact (h1). Qed.
Lemma lem4428971 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (h1 : term375 A K x x' k s t i) : term375 A K x x' k s t i.
Proof. exact (h1). Qed.
Lemma lem4428972 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term372 A K x x' k s t i x''.
Proof. exact (h1). Qed.
Lemma lem4428979 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4428980 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4428979 K (A -> Prop) f x). Qed.
Lemma lem4428981 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4428980 A K s i). Qed.
Lemma lem4428982 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4428983 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (s i x) = (@I (K -> A -> Prop) s i x).
Proof. exact (MK_COMB (@lem4428981 A K s i) (@lem4428982 A x)). Qed.
Lemma lem4428985 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4428986 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4428985 A Prop f x). Qed.
Lemma lem4428987 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (@I (K -> A -> Prop) s i x) = (term392 A K s i x).
Proof. exact (@lem4428986 A (@I (K -> A -> Prop) s i) x). Qed.
Lemma lem4428989 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (s i x) = (term392 A K s i x).
Proof. exact (TRANS (@lem4428983 A K s i x) (@lem4428987 A K s i x)). Qed.
Lemma lem4428990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4428997 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4428998 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4428997 K (A -> Prop) f x). Qed.
Lemma lem4428999 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4428998 A K t i). Qed.
Lemma lem4429000 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4429001 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (t i x) = (@I (K -> A -> Prop) t i x).
Proof. exact (MK_COMB (@lem4428999 A K t i) (@lem4429000 A x)). Qed.
Lemma lem4429003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429004 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429003 A Prop f x). Qed.
Lemma lem4429005 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (@I (K -> A -> Prop) t i x) = (term392 A K t i x).
Proof. exact (@lem4429004 A (@I (K -> A -> Prop) t i) x). Qed.
Lemma lem4429007 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (t i x) = (term392 A K t i x).
Proof. exact (TRANS (@lem4429001 A K t i x) (@lem4429005 A K t i x)). Qed.
Lemma lem4429008 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term393 A K t i x) = (term394 A K t i x).
Proof. exact (MK_COMB (@lem4428990) (@lem4429007 A K t i x)). Qed.
Lemma lem4429009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4429010 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (term395 A K t i x) = (term396 A K t i x).
Proof. exact (MK_COMB (@lem4429009) (@lem4429008 A K t i x)). Qed.
Lemma lem4429011 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term382 A K t s i x) = (term397 A K t s i x).
Proof. exact (MK_COMB (@lem4429010 A K t i x) (@lem4428989 A K s i x)). Qed.
Lemma lem4429012 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term383 A K t s i) = (term398 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4429011 A K t s i x)). Qed.
Lemma lem4429013 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429014 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term384 A K t s i) = (term399 A K t s i).
Proof. exact (MK_COMB (@lem4429013 A) (@lem4429012 A K t s i)). Qed.
Lemma lem4429015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4429020 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429021 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4429020 K Prop f x). Qed.
Lemma lem4429023 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4429021 K k i). Qed.
Lemma lem4429024 {K : Type'} (k : K -> Prop) (i : K) : (term400 K k i) = (term401 K k i).
Proof. exact (MK_COMB (@lem4429015) (@lem4429023 K k i)). Qed.
Lemma lem4429025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4429026 {K : Type'} (k : K -> Prop) (i : K) : (term385 K k i) = (term402 K k i).
Proof. exact (MK_COMB (@lem4429025) (@lem4429024 K k i)). Qed.
Lemma lem4429027 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term387 A K k t s i) = (term403 A K k t s i).
Proof. exact (MK_COMB (@lem4429026 K k i) (@lem4429014 A K t s i)). Qed.
Lemma lem4429028 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term388 A K k t s) = (term404 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4429027 A K k t s i)). Qed.
Lemma lem4429029 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429030 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term389 A K k t s) = (term405 A K k t s).
Proof. exact (MK_COMB (@lem4429029 K) (@lem4429028 A K k t s)). Qed.
Lemma lem4429037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429038 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429037 K (A -> Prop) f x). Qed.
Lemma lem4429039 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4429038 A K t i). Qed.
Lemma lem4429040 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4429041 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (t i x) = (@I (K -> A -> Prop) t i x).
Proof. exact (MK_COMB (@lem4429039 A K t i) (@lem4429040 A x)). Qed.
Lemma lem4429043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429044 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429043 A Prop f x). Qed.
Lemma lem4429045 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (@I (K -> A -> Prop) t i x) = (term392 A K t i x).
Proof. exact (@lem4429044 A (@I (K -> A -> Prop) t i) x). Qed.
Lemma lem4429047 {A K : Type'} (t : type1470 A K) (i : K) (x : A) : (t i x) = (term392 A K t i x).
Proof. exact (TRANS (@lem4429041 A K t i x) (@lem4429045 A K t i x)). Qed.
Lemma lem4429048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4429055 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429056 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429055 K (A -> Prop) f x). Qed.
Lemma lem4429057 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4429056 A K s i). Qed.
Lemma lem4429058 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4429059 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (s i x) = (@I (K -> A -> Prop) s i x).
Proof. exact (MK_COMB (@lem4429057 A K s i) (@lem4429058 A x)). Qed.
Lemma lem4429061 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429062 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429061 A Prop f x). Qed.
Lemma lem4429063 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (@I (K -> A -> Prop) s i x) = (term392 A K s i x).
Proof. exact (@lem4429062 A (@I (K -> A -> Prop) s i) x). Qed.
Lemma lem4429065 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (s i x) = (term392 A K s i x).
Proof. exact (TRANS (@lem4429059 A K s i x) (@lem4429063 A K s i x)). Qed.
Lemma lem4429066 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term393 A K s i x) = (term394 A K s i x).
Proof. exact (MK_COMB (@lem4429048) (@lem4429065 A K s i x)). Qed.
Lemma lem4429067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4429068 {A K : Type'} (s : type1470 A K) (i : K) (x : A) : (term395 A K s i x) = (term396 A K s i x).
Proof. exact (MK_COMB (@lem4429067) (@lem4429066 A K s i x)). Qed.
Lemma lem4429069 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term382 A K s t i x) = (term397 A K s t i x).
Proof. exact (MK_COMB (@lem4429068 A K s i x) (@lem4429047 A K t i x)). Qed.
Lemma lem4429070 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term383 A K s t i) = (term398 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4429069 A K s t i x)). Qed.
Lemma lem4429071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429072 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term384 A K s t i) = (term399 A K s t i).
Proof. exact (MK_COMB (@lem4429071 A) (@lem4429070 A K s t i)). Qed.
Lemma lem4429073 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4429078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429079 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4429078 K Prop f x). Qed.
Lemma lem4429081 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4429079 K k i). Qed.
Lemma lem4429082 {K : Type'} (k : K -> Prop) (i : K) : (term400 K k i) = (term401 K k i).
Proof. exact (MK_COMB (@lem4429073) (@lem4429081 K k i)). Qed.
Lemma lem4429083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4429084 {K : Type'} (k : K -> Prop) (i : K) : (term385 K k i) = (term402 K k i).
Proof. exact (MK_COMB (@lem4429083) (@lem4429082 K k i)). Qed.
Lemma lem4429085 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term387 A K k s t i) = (term403 A K k s t i).
Proof. exact (MK_COMB (@lem4429084 K k i) (@lem4429072 A K s t i)). Qed.
Lemma lem4429086 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term388 A K k s t) = (term404 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4429085 A K k s t i)). Qed.
Lemma lem4429087 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429088 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term389 A K k s t) = (term405 A K k s t).
Proof. exact (MK_COMB (@lem4429087 K) (@lem4429086 A K k s t)). Qed.
Lemma lem4429089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429090 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term390 A K k s t) = (term406 A K k s t).
Proof. exact (MK_COMB (@lem4429089) (@lem4429088 A K k s t)). Qed.
Lemma lem4429091 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term391 A K k t s) = (term407 A K k t s).
Proof. exact (MK_COMB (@lem4429090 A K k s t) (@lem4429030 A K k t s)). Qed.
Lemma lem4429092 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term407 A K k t s.
Proof. exact (EQ_MP (@lem4429091 A K k t s) (@lem4428968 A K k t s h1)). Qed.
Lemma lem4429099 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429100 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429099 K (A -> Prop) f x). Qed.
Lemma lem4429101 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4429100 A K t i). Qed.
Lemma lem4429102 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (eq_refl x''). Qed.
Lemma lem4429103 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (t i x'') = (@I (K -> A -> Prop) t i x'').
Proof. exact (MK_COMB (@lem4429101 A K t i) (@lem4429102 A x'')). Qed.
Lemma lem4429105 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429106 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429105 A Prop f x). Qed.
Lemma lem4429107 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (@I (K -> A -> Prop) t i x'') = (term392 A K t i x'').
Proof. exact (@lem4429106 A (@I (K -> A -> Prop) t i) x''). Qed.
Lemma lem4429109 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (t i x'') = (term392 A K t i x'').
Proof. exact (TRANS (@lem4429103 A K t i x'') (@lem4429107 A K t i x'')). Qed.
Lemma lem4429110 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4429117 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429118 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429117 K (A -> Prop) f x). Qed.
Lemma lem4429119 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4429118 A K s i). Qed.
Lemma lem4429120 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (eq_refl x''). Qed.
Lemma lem4429121 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (s i x'') = (@I (K -> A -> Prop) s i x'').
Proof. exact (MK_COMB (@lem4429119 A K s i) (@lem4429120 A x'')). Qed.
Lemma lem4429123 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429124 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429123 A Prop f x). Qed.
Lemma lem4429125 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (@I (K -> A -> Prop) s i x'') = (term392 A K s i x'').
Proof. exact (@lem4429124 A (@I (K -> A -> Prop) s i) x''). Qed.
Lemma lem4429127 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (s i x'') = (term392 A K s i x'').
Proof. exact (TRANS (@lem4429121 A K s i x'') (@lem4429125 A K s i x'')). Qed.
Lemma lem4429128 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term393 A K s i x'') = (term394 A K s i x'').
Proof. exact (MK_COMB (@lem4429110) (@lem4429127 A K s i x'')). Qed.
Lemma lem4429129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429130 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term408 A K s i x'') = (term409 A K s i x'').
Proof. exact (MK_COMB (@lem4429129) (@lem4429128 A K s i x'')). Qed.
Lemma lem4429131 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term243 A K s t i x'') = (term410 A K s t i x'').
Proof. exact (MK_COMB (@lem4429130 A K s i x'') (@lem4429109 A K t i x'')). Qed.
Lemma lem4429132 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4429139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429140 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429139 K (A -> Prop) f x). Qed.
Lemma lem4429141 {A K : Type'} (t : type1470 A K) (i : K) : (t i) = (@I (K -> A -> Prop) t i).
Proof. exact (@lem4429140 A K t i). Qed.
Lemma lem4429142 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (eq_refl x''). Qed.
Lemma lem4429143 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (t i x'') = (@I (K -> A -> Prop) t i x'').
Proof. exact (MK_COMB (@lem4429141 A K t i) (@lem4429142 A x'')). Qed.
Lemma lem4429145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429146 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429145 A Prop f x). Qed.
Lemma lem4429147 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (@I (K -> A -> Prop) t i x'') = (term392 A K t i x'').
Proof. exact (@lem4429146 A (@I (K -> A -> Prop) t i) x''). Qed.
Lemma lem4429149 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (t i x'') = (term392 A K t i x'').
Proof. exact (TRANS (@lem4429143 A K t i x'') (@lem4429147 A K t i x'')). Qed.
Lemma lem4429150 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (term393 A K t i x'') = (term394 A K t i x'').
Proof. exact (MK_COMB (@lem4429132) (@lem4429149 A K t i x'')). Qed.
Lemma lem4429157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429158 {A K : Type'} (f : type1470 A K) (x : K) : (f x) = (@I (K -> A -> Prop) f x).
Proof. exact (@lem4429157 K (A -> Prop) f x). Qed.
Lemma lem4429159 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (@I (K -> A -> Prop) s i).
Proof. exact (@lem4429158 A K s i). Qed.
Lemma lem4429160 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (eq_refl x''). Qed.
Lemma lem4429161 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (s i x'') = (@I (K -> A -> Prop) s i x'').
Proof. exact (MK_COMB (@lem4429159 A K s i) (@lem4429160 A x'')). Qed.
Lemma lem4429163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429164 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4429163 A Prop f x). Qed.
Lemma lem4429165 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (@I (K -> A -> Prop) s i x'') = (term392 A K s i x'').
Proof. exact (@lem4429164 A (@I (K -> A -> Prop) s i) x''). Qed.
Lemma lem4429167 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (s i x'') = (term392 A K s i x'').
Proof. exact (TRANS (@lem4429161 A K s i x'') (@lem4429165 A K s i x'')). Qed.
Lemma lem4429168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429169 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term411 A K s i x'') = (term412 A K s i x'').
Proof. exact (MK_COMB (@lem4429168) (@lem4429167 A K s i x'')). Qed.
Lemma lem4429170 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term239 A K s t i x'') = (term413 A K s t i x'').
Proof. exact (MK_COMB (@lem4429169 A K s i x'') (@lem4429150 A K t i x'')). Qed.
Lemma lem4429171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4429172 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term241 A K s t i x'') = (term414 A K s t i x'').
Proof. exact (MK_COMB (@lem4429171) (@lem4429170 A K s t i x'')). Qed.
Lemma lem4429173 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term209 A K s t i x'') = (term415 A K s t i x'').
Proof. exact (MK_COMB (@lem4429172 A K s t i x'') (@lem4429131 A K s t i x'')). Qed.
Lemma lem4429178 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4429179 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem4429178 K Prop f x). Qed.
Lemma lem4429181 {K : Type'} (k : K -> Prop) (i : K) : (k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4429179 K k i). Qed.
Lemma lem4429182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429183 {K : Type'} (k : K -> Prop) (i : K) : (term219 K k i) = (term416 K k i).
Proof. exact (MK_COMB (@lem4429182) (@lem4429181 K k i)). Qed.
Lemma lem4429184 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term274 A K k s t i x'') = (term417 A K k s t i x'').
Proof. exact (MK_COMB (@lem4429183 K k i) (@lem4429173 A K s t i x'')). Qed.
Lemma lem4429193 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (x' : K -> A) : (term294 A K k t x') = (term294 A K k t x').
Proof. exact (eq_refl (term294 A K k t x')). Qed.
Lemma lem4429194 {A K : Type'} (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term320 A K x' k s t i x'') = (term418 A K x' k s t i x'').
Proof. exact (MK_COMB (@lem4429193 A K k t x') (@lem4429184 A K k s t i x'')). Qed.
Lemma lem4429203 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term294 A K k s x) = (term294 A K k s x).
Proof. exact (eq_refl (term294 A K k s x)). Qed.
Lemma lem4429204 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) : (term372 A K x x' k s t i x'') = (term419 A K x x' k s t i x'').
Proof. exact (MK_COMB (@lem4429203 A K k s x) (@lem4429194 A K x' k s t i x'')). Qed.
Lemma lem4429205 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term419 A K x x' k s t i x''.
Proof. exact (EQ_MP (@lem4429204 A K x x' k s t i x'') (@lem4428972 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429206 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term418 A K x' k s t i x''.
Proof. exact (proj2 (@lem4429205 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429208 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term417 A K k s t i x''.
Proof. exact (proj2 (@lem4429206 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429210 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term415 A K s t i x''.
Proof. exact (proj2 (@lem4429208 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429212 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term405 A K k t s.
Proof. exact (proj2 (@lem4429092 A K k t s h1)). Qed.
Lemma lem4429213 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term405 A K k s t.
Proof. exact (proj1 (@lem4429092 A K k t s h1)). Qed.
Lemma lem4429214 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term413 A K s t i x''.
Proof. exact (h1). Qed.
Lemma lem4429215 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term410 A K s t i x''.
Proof. exact (h1). Qed.
Lemma lem4429233 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4429234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (@lem4429233 A P Q). Qed.
Lemma lem4429235 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term422 A K k s t i) = (term423 A K k s t i).
Proof. exact (@lem4429234 A (term401 K k i) (term398 A K s t i)). Qed.
Lemma lem4429236 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term424 A K s t i x) = (term397 A K s t i x).
Proof. exact (eq_refl (term424 A K s t i x)). Qed.
Lemma lem4429237 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term425 A K s t i) = (term398 A K s t i).
Proof. exact (fun_ext (fun x : A => @lem4429236 A K s t i x)). Qed.
Lemma lem4429238 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429239 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) : (term426 A K s t i) = (term399 A K s t i).
Proof. exact (MK_COMB (@lem4429238 A) (@lem4429237 A K s t i)). Qed.
Lemma lem4429240 {K : Type'} (k : K -> Prop) (i : K) : (term402 K k i) = (term402 K k i).
Proof. exact (eq_refl (term402 K k i)). Qed.
Lemma lem4429241 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term422 A K k s t i) = (term403 A K k s t i).
Proof. exact (MK_COMB (@lem4429240 K k i) (@lem4429239 A K s t i)). Qed.
Lemma lem4429242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4429243 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term427 A K k s t i) = (term428 A K k s t i).
Proof. exact (MK_COMB (@lem4429242) (@lem4429241 A K k s t i)). Qed.
Lemma lem4429244 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term424 A K s t i x) = (term397 A K s t i x).
Proof. exact (eq_refl (term424 A K s t i x)). Qed.
Lemma lem4429245 {K : Type'} (k : K -> Prop) (i : K) : (term402 K k i) = (term402 K k i).
Proof. exact (eq_refl (term402 K k i)). Qed.
Lemma lem4429246 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term429 A K k s t i x) = (term430 A K k s t i x).
Proof. exact (MK_COMB (@lem4429245 K k i) (@lem4429244 A K s t i x)). Qed.
Lemma lem4429247 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term431 A K k s t i) = (term432 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4429246 A K k s t i x)). Qed.
Lemma lem4429248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429249 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term423 A K k s t i) = (term433 A K k s t i).
Proof. exact (MK_COMB (@lem4429248 A) (@lem4429247 A K k s t i)). Qed.
Lemma lem4429250 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : ((term422 A K k s t i) = (term423 A K k s t i)) = ((term403 A K k s t i) = (term433 A K k s t i)).
Proof. exact (MK_COMB (@lem4429243 A K k s t i) (@lem4429249 A K k s t i)). Qed.
Lemma lem4429251 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term403 A K k s t i) = (term433 A K k s t i).
Proof. exact (EQ_MP (@lem4429250 A K k s t i) (@lem4429235 A K k s t i)). Qed.
Lemma lem4429252 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term404 A K k s t) = (term434 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4429251 A K k s t i)). Qed.
Lemma lem4429253 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429254 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term405 A K k s t) = (term435 A K k s t).
Proof. exact (MK_COMB (@lem4429253 K) (@lem4429252 A K k s t)). Qed.
Lemma lem4429267 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x : A) : (term430 A K k s t i x) = (term430 A K k s t i x).
Proof. exact (eq_refl (term430 A K k s t i x)). Qed.
Lemma lem4429268 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term432 A K k s t i) = (term432 A K k s t i).
Proof. exact (fun_ext (fun x : A => @lem4429267 A K k s t i x)). Qed.
Lemma lem4429269 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429270 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) : (term433 A K k s t i) = (term433 A K k s t i).
Proof. exact (MK_COMB (@lem4429269 A) (@lem4429268 A K k s t i)). Qed.
Lemma lem4429271 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term434 A K k s t) = (term434 A K k s t).
Proof. exact (fun_ext (fun i : K => @lem4429270 A K k s t i)). Qed.
Lemma lem4429272 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429273 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term435 A K k s t) = (term435 A K k s t).
Proof. exact (MK_COMB (@lem4429272 K) (@lem4429271 A K k s t)). Qed.
Lemma lem4429274 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : (term405 A K k s t) = (term435 A K k s t).
Proof. exact (TRANS (@lem4429254 A K k s t) (@lem4429273 A K k s t)). Qed.
Lemma lem4429275 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term435 A K k s t.
Proof. exact (EQ_MP (@lem4429274 A K k s t) (@lem4429213 A K k t s h1)). Qed.
Lemma lem4429385 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4429386 {A : Type'} (P : Prop) (Q : A -> Prop) : (term420 A P Q) = (term421 A P Q).
Proof. exact (@lem4429385 A P Q). Qed.
Lemma lem4429387 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term422 A K k t s i) = (term423 A K k t s i).
Proof. exact (@lem4429386 A (term401 K k i) (term398 A K t s i)). Qed.
Lemma lem4429388 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term424 A K t s i x) = (term397 A K t s i x).
Proof. exact (eq_refl (term424 A K t s i x)). Qed.
Lemma lem4429389 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term425 A K t s i) = (term398 A K t s i).
Proof. exact (fun_ext (fun x : A => @lem4429388 A K t s i x)). Qed.
Lemma lem4429390 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429391 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) : (term426 A K t s i) = (term399 A K t s i).
Proof. exact (MK_COMB (@lem4429390 A) (@lem4429389 A K t s i)). Qed.
Lemma lem4429392 {K : Type'} (k : K -> Prop) (i : K) : (term402 K k i) = (term402 K k i).
Proof. exact (eq_refl (term402 K k i)). Qed.
Lemma lem4429393 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term422 A K k t s i) = (term403 A K k t s i).
Proof. exact (MK_COMB (@lem4429392 K k i) (@lem4429391 A K t s i)). Qed.
Lemma lem4429394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4429395 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term427 A K k t s i) = (term428 A K k t s i).
Proof. exact (MK_COMB (@lem4429394) (@lem4429393 A K k t s i)). Qed.
Lemma lem4429396 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term424 A K t s i x) = (term397 A K t s i x).
Proof. exact (eq_refl (term424 A K t s i x)). Qed.
Lemma lem4429397 {K : Type'} (k : K -> Prop) (i : K) : (term402 K k i) = (term402 K k i).
Proof. exact (eq_refl (term402 K k i)). Qed.
Lemma lem4429398 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term429 A K k t s i x) = (term430 A K k t s i x).
Proof. exact (MK_COMB (@lem4429397 K k i) (@lem4429396 A K t s i x)). Qed.
Lemma lem4429399 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term431 A K k t s i) = (term432 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4429398 A K k t s i x)). Qed.
Lemma lem4429400 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429401 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term423 A K k t s i) = (term433 A K k t s i).
Proof. exact (MK_COMB (@lem4429400 A) (@lem4429399 A K k t s i)). Qed.
Lemma lem4429402 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : ((term422 A K k t s i) = (term423 A K k t s i)) = ((term403 A K k t s i) = (term433 A K k t s i)).
Proof. exact (MK_COMB (@lem4429395 A K k t s i) (@lem4429401 A K k t s i)). Qed.
Lemma lem4429403 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term403 A K k t s i) = (term433 A K k t s i).
Proof. exact (EQ_MP (@lem4429402 A K k t s i) (@lem4429387 A K k t s i)). Qed.
Lemma lem4429404 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term404 A K k t s) = (term434 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4429403 A K k t s i)). Qed.
Lemma lem4429405 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429406 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term405 A K k t s) = (term435 A K k t s).
Proof. exact (MK_COMB (@lem4429405 K) (@lem4429404 A K k t s)). Qed.
Lemma lem4429419 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) (x : A) : (term430 A K k t s i x) = (term430 A K k t s i x).
Proof. exact (eq_refl (term430 A K k t s i x)). Qed.
Lemma lem4429420 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term432 A K k t s i) = (term432 A K k t s i).
Proof. exact (fun_ext (fun x : A => @lem4429419 A K k t s i x)). Qed.
Lemma lem4429421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4429422 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (i : K) : (term433 A K k t s i) = (term433 A K k t s i).
Proof. exact (MK_COMB (@lem4429421 A) (@lem4429420 A K k t s i)). Qed.
Lemma lem4429423 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term434 A K k t s) = (term434 A K k t s).
Proof. exact (fun_ext (fun i : K => @lem4429422 A K k t s i)). Qed.
Lemma lem4429424 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4429425 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term435 A K k t s) = (term435 A K k t s).
Proof. exact (MK_COMB (@lem4429424 K) (@lem4429423 A K k t s)). Qed.
Lemma lem4429426 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term405 A K k t s) = (term435 A K k t s).
Proof. exact (TRANS (@lem4429406 A K k t s) (@lem4429425 A K k t s)). Qed.
Lemma lem4429427 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term435 A K k t s.
Proof. exact (EQ_MP (@lem4429426 A K k t s) (@lem4429212 A K k t s h1)). Qed.
Lemma lem4429436 {A K : Type'} (_50973 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term436 A K k s t _50973.
Proof. exact (@lem4429275 A K k t s h1 _50973). Qed.
Lemma lem4429437 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50973 : K) : (term436 A K k s t _50973) = (term433 A K k s t _50973).
Proof. exact (eq_refl (term436 A K k s t _50973)). Qed.
Lemma lem4429438 {A K : Type'} (_50973 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term433 A K k s t _50973.
Proof. exact (EQ_MP (@lem4429437 A K k s t _50973) (@lem4429436 A K _50973 k t s h1)). Qed.
Lemma lem4429439 {A K : Type'} (_50973 : K) (_50974 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term437 A K k s t _50973 _50974.
Proof. exact (@lem4429438 A K _50973 k t s h1 _50974). Qed.
Lemma lem4429440 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50973 : K) (_50974 : A) : (term437 A K k s t _50973 _50974) = (term430 A K k s t _50973 _50974).
Proof. exact (eq_refl (term437 A K k s t _50973 _50974)). Qed.
Lemma lem4429454 {A K : Type'} (_50979 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term436 A K k t s _50979.
Proof. exact (@lem4429427 A K k t s h1 _50979). Qed.
Lemma lem4429455 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_50979 : K) : (term436 A K k t s _50979) = (term433 A K k t s _50979).
Proof. exact (eq_refl (term436 A K k t s _50979)). Qed.
Lemma lem4429456 {A K : Type'} (_50979 : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term433 A K k t s _50979.
Proof. exact (EQ_MP (@lem4429455 A K k t s _50979) (@lem4429454 A K _50979 k t s h1)). Qed.
Lemma lem4429457 {A K : Type'} (_50979 : K) (_50980 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term437 A K k t s _50979 _50980.
Proof. exact (@lem4429456 A K _50979 k t s h1 _50980). Qed.
Lemma lem4429458 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_50979 : K) (_50980 : A) : (term437 A K k t s _50979 _50980) = (term430 A K k t s _50979 _50980).
Proof. exact (eq_refl (term437 A K k t s _50979 _50980)). Qed.
Lemma lem4429475 {A K : Type'} (_50973 : K) (_50974 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term430 A K k s t _50973 _50974.
Proof. exact (EQ_MP (@lem4429440 A K k s t _50973 _50974) (@lem4429439 A K _50973 _50974 k t s h1)). Qed.
Lemma lem4429489 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term394 A K t i x''.
Proof. exact (proj2 (@lem4429214 A K s t i x'' h1)). Qed.
Lemma lem4429515 {A K : Type'} (_50979 : K) (_50980 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term430 A K k t s _50979 _50980.
Proof. exact (EQ_MP (@lem4429458 A K k t s _50979 _50980) (@lem4429457 A K _50979 _50980 k t s h1)). Qed.
Lemma lem4429517 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term394 A K s i x''.
Proof. exact (proj1 (@lem4429215 A K s t i x'' h1)). Qed.
Lemma lem4429521 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4429208 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429522 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term438 K k i.
Proof. exact (fun h0 : term401 K k i => @lem4429521 A K x x' k s t i x'' h1). Qed.
Lemma lem4429524 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429525 {K : Type'} (k : K -> Prop) (i : K) : (term438 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4429524 (@I (K -> Prop) k i)). Qed.
Lemma lem4429526 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4429525 K k i) (@lem4429522 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429528 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term392 A K s i x''.
Proof. exact (proj1 (@lem4429214 A K s t i x'' h1)). Qed.
Lemma lem4429529 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term440 A K s i x''.
Proof. exact (fun h0 : term394 A K s i x'' => @lem4429528 A K s t i x'' h1). Qed.
Lemma lem4429531 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429532 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term440 A K s i x'') = (term392 A K s i x'').
Proof. exact (@lem4429531 (term392 A K s i x'')). Qed.
Lemma lem4429533 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term392 A K s i x''.
Proof. exact (EQ_MP (@lem4429532 A K s i x'') (@lem4429529 A K s t i x'' h1)). Qed.
Lemma lem4429539 (q : Prop) (p : Prop) (r : Prop) : (term441 p q r) = (term441 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4429540 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_50973 : K) (_50974 : A) : (term430 A K k s t _50973 _50974) = (term442 A K s k t _50973 _50974).
Proof. exact (@lem4429539 (term394 A K s _50973 _50974) (term401 K k _50973) (term392 A K t _50973 _50974)). Qed.
Lemma lem4429554 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4429555 {A K : Type'} (t : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term443 A K k t _50973 _50974) = (term444 A K t _50974 k _50973).
Proof. exact (@lem4429554 (term392 A K t _50973 _50974) (term401 K k _50973)). Qed.
Lemma lem4429561 {A K : Type'} (s : type1470 A K) (_50973 : K) (_50974 : A) : (term396 A K s _50973 _50974) = (term396 A K s _50973 _50974).
Proof. exact (eq_refl (term396 A K s _50973 _50974)). Qed.
Lemma lem4429562 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term442 A K s k t _50973 _50974) = (term445 A K s t _50974 k _50973).
Proof. exact (MK_COMB (@lem4429561 A K s _50973 _50974) (@lem4429555 A K t _50974 k _50973)). Qed.
Lemma lem4429566 (q : Prop) (p : Prop) (r : Prop) : (term441 p q r) = (term441 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4429567 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term445 A K s t _50974 k _50973) = (term446 A K t s _50974 k _50973).
Proof. exact (@lem4429566 (term392 A K t _50973 _50974) (term394 A K s _50973 _50974) (term401 K k _50973)). Qed.
Lemma lem4429583 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term442 A K s k t _50973 _50974) = (term446 A K t s _50974 k _50973).
Proof. exact (TRANS (@lem4429562 A K s t _50974 k _50973) (@lem4429567 A K t s _50974 k _50973)). Qed.
Lemma lem4429584 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term430 A K k s t _50973 _50974) = (term446 A K t s _50974 k _50973).
Proof. exact (TRANS (@lem4429540 A K s k t _50973 _50974) (@lem4429583 A K t s _50974 k _50973)). Qed.
Lemma lem4429585 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4429586 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term447 A K k s t _50973 _50974) = (term448 A K t s _50974 k _50973).
Proof. exact (MK_COMB (@lem4429585) (@lem4429584 A K t s _50974 k _50973)). Qed.
Lemma lem4429600 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4429601 {A K : Type'} (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term449 A K k s _50973 _50974) = (term450 A K s _50974 k _50973).
Proof. exact (@lem4429600 (term394 A K s _50973 _50974) (term401 K k _50973)). Qed.
Lemma lem4429607 {A K : Type'} (t : type1470 A K) (_50973 : K) (_50974 : A) : (term451 A K t _50973 _50974) = (term451 A K t _50973 _50974).
Proof. exact (eq_refl (term451 A K t _50973 _50974)). Qed.
Lemma lem4429608 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : (term452 A K t k s _50973 _50974) = (term446 A K t s _50974 k _50973).
Proof. exact (MK_COMB (@lem4429607 A K t _50973 _50974) (@lem4429601 A K s _50974 k _50973)). Qed.
Lemma lem4429619 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : ((term430 A K k s t _50973 _50974) = (term452 A K t k s _50973 _50974)) = ((term446 A K t s _50974 k _50973) = (term446 A K t s _50974 k _50973)).
Proof. exact (MK_COMB (@lem4429586 A K t s _50974 k _50973) (@lem4429608 A K t s _50974 k _50973)). Qed.
Lemma lem4429621 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4429622 (x : Prop) : (x = x) = True.
Proof. exact (@lem4429621 Prop x). Qed.
Lemma lem4429623 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50974 : A) (k : K -> Prop) (_50973 : K) : ((term446 A K t s _50974 k _50973) = (term446 A K t s _50974 k _50973)) = True.
Proof. exact (@lem4429622 (term446 A K t s _50974 k _50973)). Qed.
Lemma lem4429624 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : ((term430 A K k s t _50973 _50974) = (term452 A K t k s _50973 _50974)) = True.
Proof. exact (TRANS (@lem4429619 A K t s _50974 k _50973) (@lem4429623 A K t s _50974 k _50973)). Qed.
Lemma lem4429625 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : True = ((term430 A K k s t _50973 _50974) = (term452 A K t k s _50973 _50974)).
Proof. exact (SYM (@lem4429624 A K t k s _50973 _50974)). Qed.
Lemma lem4429626 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : (term430 A K k s t _50973 _50974) = (term452 A K t k s _50973 _50974).
Proof. exact (EQ_MP (@lem4429625 A K t k s _50973 _50974) (@lem0)). Qed.
Lemma lem4429627 {A K : Type'} (_50973 : K) (_50974 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term452 A K t k s _50973 _50974.
Proof. exact (EQ_MP (@lem4429626 A K t k s _50973 _50974) (@lem4429475 A K _50973 _50974 k t s h1)). Qed.
Lemma lem4429629 (b : Prop) (a : Prop) : (a \/ b) = (term453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4429630 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50973 : K) (_50974 : A) : (term452 A K t k s _50973 _50974) = (term454 A K k s t _50973 _50974).
Proof. exact (@lem4429629 (term449 A K k s _50973 _50974) (term392 A K t _50973 _50974)). Qed.
Lemma lem4429632 (a : Prop) (b : Prop) : (term455 a b) = (term456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4429633 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : (term457 A K k s _50973 _50974) = (term458 A K k s _50973 _50974).
Proof. exact (@lem4429632 (term401 K k _50973) (term394 A K s _50973 _50974)). Qed.
Lemma lem4429635 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4429636 {K : Type'} (k : K -> Prop) (_50973 : K) : (term459 K k _50973) = (@I (K -> Prop) k _50973).
Proof. exact (@lem4429635 (@I (K -> Prop) k _50973)). Qed.
Lemma lem4429637 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429638 {K : Type'} (k : K -> Prop) (_50973 : K) : (term460 K k _50973) = (term416 K k _50973).
Proof. exact (MK_COMB (@lem4429637) (@lem4429636 K k _50973)). Qed.
Lemma lem4429640 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4429641 {A K : Type'} (s : type1470 A K) (_50973 : K) (_50974 : A) : (term461 A K s _50973 _50974) = (term392 A K s _50973 _50974).
Proof. exact (@lem4429640 (term392 A K s _50973 _50974)). Qed.
Lemma lem4429642 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : (term458 A K k s _50973 _50974) = (term462 A K k s _50973 _50974).
Proof. exact (MK_COMB (@lem4429638 K k _50973) (@lem4429641 A K s _50973 _50974)). Qed.
Lemma lem4429643 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : (term457 A K k s _50973 _50974) = (term462 A K k s _50973 _50974).
Proof. exact (TRANS (@lem4429633 A K k s _50973 _50974) (@lem4429642 A K k s _50973 _50974)). Qed.
Lemma lem4429644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4429645 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (_50973 : K) (_50974 : A) : (term463 A K k s _50973 _50974) = (term464 A K k s _50973 _50974).
Proof. exact (MK_COMB (@lem4429644) (@lem4429643 A K k s _50973 _50974)). Qed.
Lemma lem4429646 {A K : Type'} (t : type1470 A K) (_50973 : K) (_50974 : A) : (term392 A K t _50973 _50974) = (term392 A K t _50973 _50974).
Proof. exact (eq_refl (term392 A K t _50973 _50974)). Qed.
Lemma lem4429647 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50973 : K) (_50974 : A) : (term454 A K k s t _50973 _50974) = (term465 A K k s t _50973 _50974).
Proof. exact (MK_COMB (@lem4429645 A K k s _50973 _50974) (@lem4429646 A K t _50973 _50974)). Qed.
Lemma lem4429648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (_50973 : K) (_50974 : A) : (term452 A K t k s _50973 _50974) = (term465 A K k s t _50973 _50974).
Proof. exact (TRANS (@lem4429630 A K k s t _50973 _50974) (@lem4429647 A K k s t _50973 _50974)). Qed.
Lemma lem4429650 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') (h2 : term372 A K x x' k s t i x'') : term462 A K k s i x''.
Proof. exact (conj (@lem4429526 A K x x' k s t i x'' h2) (@lem4429533 A K s t i x'' h1)). Qed.
Lemma lem4429652 {A K : Type'} (_50973 : K) (_50974 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k s t _50973 _50974.
Proof. exact (EQ_MP (@lem4429648 A K k s t _50973 _50974) (@lem4429627 A K _50973 _50974 k t s h1)). Qed.
Lemma lem4429653 {A K : Type'} (_50973 : K) (_50974 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k s t _50973 _50974.
Proof. exact (@lem4429652 A K _50973 _50974 k t s h1). Qed.
Lemma lem4429654 {A K : Type'} (i : K) (x'' : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k s t i x''.
Proof. exact (@lem4429653 A K i x'' k t s h1). Qed.
Lemma lem4429657 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term392 A K t i x''.
Proof. exact (@lem4429654 A K i x'' k t s h1 (@lem4429650 A K x x' k s t i x'' h2 h3)). Qed.
Lemma lem4429658 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term440 A K t i x''.
Proof. exact (fun h0 : term394 A K t i x'' => @lem4429657 A K x x' k s t i x'' h1 h2 h3). Qed.
Lemma lem4429660 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429661 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (term440 A K t i x'') = (term392 A K t i x'').
Proof. exact (@lem4429660 (term392 A K t i x'')). Qed.
Lemma lem4429662 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term392 A K t i x''.
Proof. exact (EQ_MP (@lem4429661 A K t i x'') (@lem4429658 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429665 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4429667 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (term394 A K t i x'') = (term466 A K t i x'').
Proof. exact (@lem4429665 (term392 A K t i x'')). Qed.
Lemma lem4429670 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term413 A K s t i x'') : term466 A K t i x''.
Proof. exact (EQ_MP (@lem4429667 A K t i x'') (@lem4429489 A K s t i x'' h1)). Qed.
Lemma lem4429673 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : False.
Proof. exact (@lem4429670 A K s t i x'' h2 (@lem4429662 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429674 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term467.
Proof. exact (fun h0 : ~ False => @lem4429673 A K x x' k s t i x'' h1 h2 h3). Qed.
Lemma lem4429676 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429677 : term467 = False.
Proof. exact (@lem4429676 False). Qed.
Lemma lem4429678 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term413 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : False.
Proof. exact (EQ_MP (@lem4429677) (@lem4429674 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429680 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : @I (K -> Prop) k i.
Proof. exact (proj1 (@lem4429208 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429681 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : term438 K k i.
Proof. exact (fun h0 : term401 K k i => @lem4429680 A K x x' k s t i x'' h1). Qed.
Lemma lem4429683 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429684 {K : Type'} (k : K -> Prop) (i : K) : (term438 K k i) = (@I (K -> Prop) k i).
Proof. exact (@lem4429683 (@I (K -> Prop) k i)). Qed.
Lemma lem4429685 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term372 A K x x' k s t i x'') : @I (K -> Prop) k i.
Proof. exact (EQ_MP (@lem4429684 K k i) (@lem4429681 A K x x' k s t i x'' h1)). Qed.
Lemma lem4429687 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term392 A K t i x''.
Proof. exact (proj2 (@lem4429215 A K s t i x'' h1)). Qed.
Lemma lem4429688 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term440 A K t i x''.
Proof. exact (fun h0 : term394 A K t i x'' => @lem4429687 A K s t i x'' h1). Qed.
Lemma lem4429690 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429691 {A K : Type'} (t : type1470 A K) (i : K) (x'' : A) : (term440 A K t i x'') = (term392 A K t i x'').
Proof. exact (@lem4429690 (term392 A K t i x'')). Qed.
Lemma lem4429692 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term392 A K t i x''.
Proof. exact (EQ_MP (@lem4429691 A K t i x'') (@lem4429688 A K s t i x'' h1)). Qed.
Lemma lem4429698 (q : Prop) (p : Prop) (r : Prop) : (term441 p q r) = (term441 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4429699 {A K : Type'} (t : type1470 A K) (k : K -> Prop) (s : type1470 A K) (_50979 : K) (_50980 : A) : (term430 A K k t s _50979 _50980) = (term442 A K t k s _50979 _50980).
Proof. exact (@lem4429698 (term394 A K t _50979 _50980) (term401 K k _50979) (term392 A K s _50979 _50980)). Qed.
Lemma lem4429713 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4429714 {A K : Type'} (s : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term443 A K k s _50979 _50980) = (term444 A K s _50980 k _50979).
Proof. exact (@lem4429713 (term392 A K s _50979 _50980) (term401 K k _50979)). Qed.
Lemma lem4429720 {A K : Type'} (t : type1470 A K) (_50979 : K) (_50980 : A) : (term396 A K t _50979 _50980) = (term396 A K t _50979 _50980).
Proof. exact (eq_refl (term396 A K t _50979 _50980)). Qed.
Lemma lem4429721 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term442 A K t k s _50979 _50980) = (term445 A K t s _50980 k _50979).
Proof. exact (MK_COMB (@lem4429720 A K t _50979 _50980) (@lem4429714 A K s _50980 k _50979)). Qed.
Lemma lem4429725 (q : Prop) (p : Prop) (r : Prop) : (term441 p q r) = (term441 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4429726 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term445 A K t s _50980 k _50979) = (term446 A K s t _50980 k _50979).
Proof. exact (@lem4429725 (term392 A K s _50979 _50980) (term394 A K t _50979 _50980) (term401 K k _50979)). Qed.
Lemma lem4429742 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term442 A K t k s _50979 _50980) = (term446 A K s t _50980 k _50979).
Proof. exact (TRANS (@lem4429721 A K t s _50980 k _50979) (@lem4429726 A K s t _50980 k _50979)). Qed.
Lemma lem4429743 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term430 A K k t s _50979 _50980) = (term446 A K s t _50980 k _50979).
Proof. exact (TRANS (@lem4429699 A K t k s _50979 _50980) (@lem4429742 A K s t _50980 k _50979)). Qed.
Lemma lem4429744 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4429745 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term447 A K k t s _50979 _50980) = (term448 A K s t _50980 k _50979).
Proof. exact (MK_COMB (@lem4429744) (@lem4429743 A K s t _50980 k _50979)). Qed.
Lemma lem4429759 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4429760 {A K : Type'} (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term449 A K k t _50979 _50980) = (term450 A K t _50980 k _50979).
Proof. exact (@lem4429759 (term394 A K t _50979 _50980) (term401 K k _50979)). Qed.
Lemma lem4429766 {A K : Type'} (s : type1470 A K) (_50979 : K) (_50980 : A) : (term451 A K s _50979 _50980) = (term451 A K s _50979 _50980).
Proof. exact (eq_refl (term451 A K s _50979 _50980)). Qed.
Lemma lem4429767 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : (term452 A K s k t _50979 _50980) = (term446 A K s t _50980 k _50979).
Proof. exact (MK_COMB (@lem4429766 A K s _50979 _50980) (@lem4429760 A K t _50980 k _50979)). Qed.
Lemma lem4429778 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : ((term430 A K k t s _50979 _50980) = (term452 A K s k t _50979 _50980)) = ((term446 A K s t _50980 k _50979) = (term446 A K s t _50980 k _50979)).
Proof. exact (MK_COMB (@lem4429745 A K s t _50980 k _50979) (@lem4429767 A K s t _50980 k _50979)). Qed.
Lemma lem4429780 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4429781 (x : Prop) : (x = x) = True.
Proof. exact (@lem4429780 Prop x). Qed.
Lemma lem4429782 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (_50980 : A) (k : K -> Prop) (_50979 : K) : ((term446 A K s t _50980 k _50979) = (term446 A K s t _50980 k _50979)) = True.
Proof. exact (@lem4429781 (term446 A K s t _50980 k _50979)). Qed.
Lemma lem4429783 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : ((term430 A K k t s _50979 _50980) = (term452 A K s k t _50979 _50980)) = True.
Proof. exact (TRANS (@lem4429778 A K s t _50980 k _50979) (@lem4429782 A K s t _50980 k _50979)). Qed.
Lemma lem4429784 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : True = ((term430 A K k t s _50979 _50980) = (term452 A K s k t _50979 _50980)).
Proof. exact (SYM (@lem4429783 A K s k t _50979 _50980)). Qed.
Lemma lem4429785 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : (term430 A K k t s _50979 _50980) = (term452 A K s k t _50979 _50980).
Proof. exact (EQ_MP (@lem4429784 A K s k t _50979 _50980) (@lem0)). Qed.
Lemma lem4429786 {A K : Type'} (_50979 : K) (_50980 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term452 A K s k t _50979 _50980.
Proof. exact (EQ_MP (@lem4429785 A K s k t _50979 _50980) (@lem4429515 A K _50979 _50980 k t s h1)). Qed.
Lemma lem4429788 (b : Prop) (a : Prop) : (a \/ b) = (term453 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4429789 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_50979 : K) (_50980 : A) : (term452 A K s k t _50979 _50980) = (term454 A K k t s _50979 _50980).
Proof. exact (@lem4429788 (term449 A K k t _50979 _50980) (term392 A K s _50979 _50980)). Qed.
Lemma lem4429791 (a : Prop) (b : Prop) : (term455 a b) = (term456 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4429792 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : (term457 A K k t _50979 _50980) = (term458 A K k t _50979 _50980).
Proof. exact (@lem4429791 (term401 K k _50979) (term394 A K t _50979 _50980)). Qed.
Lemma lem4429794 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4429795 {K : Type'} (k : K -> Prop) (_50979 : K) : (term459 K k _50979) = (@I (K -> Prop) k _50979).
Proof. exact (@lem4429794 (@I (K -> Prop) k _50979)). Qed.
Lemma lem4429796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4429797 {K : Type'} (k : K -> Prop) (_50979 : K) : (term460 K k _50979) = (term416 K k _50979).
Proof. exact (MK_COMB (@lem4429796) (@lem4429795 K k _50979)). Qed.
Lemma lem4429799 (a : Prop) : (term186 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4429800 {A K : Type'} (t : type1470 A K) (_50979 : K) (_50980 : A) : (term461 A K t _50979 _50980) = (term392 A K t _50979 _50980).
Proof. exact (@lem4429799 (term392 A K t _50979 _50980)). Qed.
Lemma lem4429801 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : (term458 A K k t _50979 _50980) = (term462 A K k t _50979 _50980).
Proof. exact (MK_COMB (@lem4429797 K k _50979) (@lem4429800 A K t _50979 _50980)). Qed.
Lemma lem4429802 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : (term457 A K k t _50979 _50980) = (term462 A K k t _50979 _50980).
Proof. exact (TRANS (@lem4429792 A K k t _50979 _50980) (@lem4429801 A K k t _50979 _50980)). Qed.
Lemma lem4429803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4429804 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (_50979 : K) (_50980 : A) : (term463 A K k t _50979 _50980) = (term464 A K k t _50979 _50980).
Proof. exact (MK_COMB (@lem4429803) (@lem4429802 A K k t _50979 _50980)). Qed.
Lemma lem4429805 {A K : Type'} (s : type1470 A K) (_50979 : K) (_50980 : A) : (term392 A K s _50979 _50980) = (term392 A K s _50979 _50980).
Proof. exact (eq_refl (term392 A K s _50979 _50980)). Qed.
Lemma lem4429806 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_50979 : K) (_50980 : A) : (term454 A K k t s _50979 _50980) = (term465 A K k t s _50979 _50980).
Proof. exact (MK_COMB (@lem4429804 A K k t _50979 _50980) (@lem4429805 A K s _50979 _50980)). Qed.
Lemma lem4429807 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (_50979 : K) (_50980 : A) : (term452 A K s k t _50979 _50980) = (term465 A K k t s _50979 _50980).
Proof. exact (TRANS (@lem4429789 A K k t s _50979 _50980) (@lem4429806 A K k t s _50979 _50980)). Qed.
Lemma lem4429809 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') (h2 : term372 A K x x' k s t i x'') : term462 A K k t i x''.
Proof. exact (conj (@lem4429685 A K x x' k s t i x'' h2) (@lem4429692 A K s t i x'' h1)). Qed.
Lemma lem4429811 {A K : Type'} (_50979 : K) (_50980 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k t s _50979 _50980.
Proof. exact (EQ_MP (@lem4429807 A K k t s _50979 _50980) (@lem4429786 A K _50979 _50980 k t s h1)). Qed.
Lemma lem4429812 {A K : Type'} (_50979 : K) (_50980 : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k t s _50979 _50980.
Proof. exact (@lem4429811 A K _50979 _50980 k t s h1). Qed.
Lemma lem4429813 {A K : Type'} (i : K) (x'' : A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term176 A K k t s) : term465 A K k t s i x''.
Proof. exact (@lem4429812 A K i x'' k t s h1). Qed.
Lemma lem4429816 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term392 A K s i x''.
Proof. exact (@lem4429813 A K i x'' k t s h1 (@lem4429809 A K x x' k s t i x'' h2 h3)). Qed.
Lemma lem4429817 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term440 A K s i x''.
Proof. exact (fun h0 : term394 A K s i x'' => @lem4429816 A K x x' k s t i x'' h1 h2 h3). Qed.
Lemma lem4429819 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429820 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term440 A K s i x'') = (term392 A K s i x'').
Proof. exact (@lem4429819 (term392 A K s i x'')). Qed.
Lemma lem4429821 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term392 A K s i x''.
Proof. exact (EQ_MP (@lem4429820 A K s i x'') (@lem4429817 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429824 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4429826 {A K : Type'} (s : type1470 A K) (i : K) (x'' : A) : (term394 A K s i x'') = (term466 A K s i x'').
Proof. exact (@lem4429824 (term392 A K s i x'')). Qed.
Lemma lem4429829 {A K : Type'} (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term410 A K s t i x'') : term466 A K s i x''.
Proof. exact (EQ_MP (@lem4429826 A K s i x'') (@lem4429517 A K s t i x'' h1)). Qed.
Lemma lem4429832 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : False.
Proof. exact (@lem4429829 A K s t i x'' h2 (@lem4429821 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429833 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : term467.
Proof. exact (fun h0 : ~ False => @lem4429832 A K x x' k s t i x'' h1 h2 h3). Qed.
Lemma lem4429835 (p : Prop) : (term439 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4429836 : term467 = False.
Proof. exact (@lem4429835 False). Qed.
Lemma lem4429837 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term410 A K s t i x'') (h3 : term372 A K x x' k s t i x'') : False.
Proof. exact (EQ_MP (@lem4429836) (@lem4429833 A K x x' k s t i x'' h1 h2 h3)). Qed.
Lemma lem4429838 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (i : K) (x'' : A) (h1 : term176 A K k t s) (h2 : term372 A K x x' k s t i x'') : False.
Proof. exact (or_elim (@lem4429210 A K x x' k s t i x'' h2) (fun h0 : term413 A K s t i x'' => @lem4429678 A K x x' k s t i x'' h1 h0 h2) (fun h0 : term410 A K s t i x'' => @lem4429837 A K x x' k s t i x'' h1 h0 h2)). Qed.
Lemma lem4429839 {A K : Type'} (x : K -> A) (x' : K -> A) (i : K) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term375 A K x x' k s t i) (h2 : term176 A K k t s) : False.
Proof. exact (ex_elim (@lem4428971 A K x x' k s t i h1) (fun x'' : A => fun h0 : term374 A K x x' k s t i x'' => @lem4429838 A K x x' k s t i x'' h2 h0)). Qed.
Lemma lem4429840 {A K : Type'} (x : K -> A) (x' : K -> A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term377 A K x x' k s t) (h2 : term176 A K k t s) : False.
Proof. exact (ex_elim (@lem4428970 A K x x' k s t h1) (fun i : K => fun h0 : term376 A K x x' k s t i => @lem4429839 A K x x' i k t s h0 h2)). Qed.
Lemma lem4429841 {A K : Type'} (x : K -> A) (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term379 A K x k s t) (h2 : term176 A K k t s) : False.
Proof. exact (ex_elim (@lem4428969 A K x k s t h1) (fun x' : K -> A => fun h0 : term378 A K x k s t x' => @lem4429840 A K x x' k t s h0 h2)). Qed.
Lemma lem4429842 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term176 A K k t s) (h2 : term163 A K k s t) : False.
Proof. exact (ex_elim (@lem4428730 A K k s t h2) (fun x : K -> A => fun h0 : term380 A K k s t x => @lem4429841 A K x k t s h0 h1)). Qed.
Lemma lem4429843 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term163 A K k s t) : term468 A K k t s.
Proof. exact (fun h0 : term176 A K k t s => @lem4429842 A K k s t h0 h1). Qed.
Lemma lem4429844 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term468 A K k t s) = (term177 A K k t s).
Proof. exact (@lem69 (term176 A K k t s)). Qed.
Lemma lem4429845 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term163 A K k s t) : term177 A K k t s.
Proof. exact (EQ_MP (@lem4429844 A K k t s) (@lem4429843 A K k s t h1)). Qed.
Lemma lem4429846 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term178 A K k t s.
Proof. exact (fun h0 : term163 A K k s t => @lem4429845 A K k s t h0). Qed.
Lemma lem4429851 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : term190 A K t s.
Proof. exact (fun k : K -> Prop => @lem4429846 A K k t s). Qed.
Lemma lem4429856 {A K : Type'} (s : type1470 A K) : term194 A K s.
Proof. exact (fun t : type1470 A K => @lem4429851 A K t s). Qed.
Lemma lem4429861 {A K : Type'} : term198 A K.
Proof. exact (fun s : type1470 A K => @lem4429856 A K s). Qed.
Lemma lem4429862 {A K : Type'} : term197 A K.
Proof. exact (EQ_MP (@lem4428229 A K) (@lem4429861 A K)). Qed.
Lemma lem4429863 {A K : Type'} (s : type1470 A K) : term469 A K s.
Proof. exact (@lem4429862 A K s). Qed.
Lemma lem4429864 {A K : Type'} (s : type1470 A K) : (term469 A K s) = (term193 A K s).
Proof. exact (eq_refl (term469 A K s)). Qed.
Lemma lem4429865 {A K : Type'} (s : type1470 A K) : term193 A K s.
Proof. exact (EQ_MP (@lem4429864 A K s) (@lem4429863 A K s)). Qed.
Lemma lem4429866 {A K : Type'} (s : type1470 A K) (t : type1470 A K) : term470 A K s t.
Proof. exact (@lem4429865 A K s t). Qed.
Lemma lem4429867 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : (term470 A K s t) = (term189 A K t s).
Proof. exact (eq_refl (term470 A K s t)). Qed.
Lemma lem4429868 {A K : Type'} (t : type1470 A K) (s : type1470 A K) : term189 A K t s.
Proof. exact (EQ_MP (@lem4429867 A K t s) (@lem4429866 A K s t)). Qed.
Lemma lem4429869 {A K : Type'} (t : type1470 A K) (s : type1470 A K) (k : K -> Prop) : term471 A K t s k.
Proof. exact (@lem4429868 A K t s k). Qed.
Lemma lem4429870 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : (term471 A K t s k) = (term180 A K k t s).
Proof. exact (eq_refl (term471 A K t s k)). Qed.
Lemma lem4429871 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term180 A K k t s.
Proof. exact (EQ_MP (@lem4429870 A K k t s) (@lem4429869 A K t s k)). Qed.
Lemma lem4429873 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term180 A K k t s.
Proof. exact (@lem4427961 A K k t s (@lem4429871 A K k t s)). Qed.
Lemma lem4429874 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term181 A K k t s) : False.
Proof. exact (@lem4429873 A K k t s (@lem4427945 A K k t s h1)). Qed.
Lemma lem4429875 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term181 A K k t s) : (term181 A K k t s) = False.
Proof. exact (prop_ext (fun h2 : term181 A K k t s => @lem4429874 A K k t s h1) (fun h2 : False => @lem4427945 A K k t s h1)). Qed.
Lemma lem4429876 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) (h1 : term181 A K k t s) : False.
Proof. exact (EQ_MP (@lem4429875 A K k t s h1) (@lem4427945 A K k t s h1)). Qed.
Lemma lem4429877 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term180 A K k t s.
Proof. exact (fun h0 : term181 A K k t s => @lem4429876 A K k t s h0). Qed.
Lemma lem4429878 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term178 A K k t s.
Proof. exact (EQ_MP (@lem4427944 A K k t s) (@lem4429877 A K k t s)). Qed.
Lemma lem4429879 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term143 A K k t s.
Proof. exact (EQ_MP (@lem4427940 A K k t s) (@lem4429878 A K k t s)). Qed.
Lemma lem4429880 {A K : Type'} (k : K -> Prop) (t : type1470 A K) (s : type1470 A K) : term142 A K k t s.
Proof. exact (EQ_MP (@lem4427705 A K k t s) (@lem4429879 A K k t s)). Qed.
Lemma lem4429881 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k s) (h3 : term11 A K k t) : term114 A K k t s.
Proof. exact (@lem4429880 A K k t s (@lem4427555 A K s k t h1 h2 h3)). Qed.
Lemma lem4429883 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k s) (h3 : term11 A K k t) : term94 A K s k t.
Proof. exact (EQ_MP (@lem4427543 A K s k t h2 h3) (@lem4429881 A K s k t h1 h2 h3)). Qed.
Lemma lem4429884 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k t) : term94 A K s k t.
Proof. exact (or_elim (@lem4426565 A K k s) (fun h0 : (@cartesian_product A K k s) = (@EMPTY (K -> A)) => @lem4427394 A K t k s h2 h0) (fun h0 : term11 A K k s => @lem4429883 A K s k t h1 h0 h2)). Qed.
Lemma lem4429885 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (t : type1470 A K) (h1 : term15 A K k s t) (h2 : term11 A K k t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t).
Proof. exact (EQ_MP (@lem4427361 A K s k t h2) (@lem4429884 A K s k t h1 h2)). Qed.
Lemma lem4429886 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term25 A K s k t).
Proof. exact (or_elim (@lem4426570 A K k t) (fun h0 : (@cartesian_product A K k t) = (@EMPTY (K -> A)) => @lem4427321 A K s k t h0) (fun h0 : term11 A K k t => @lem4429885 A K s k t h1 h0)). Qed.
Lemma lem4429887 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term15 A K k s t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t).
Proof. exact (EQ_MP (@lem4426658 A K k s t h1) (@lem4429886 A K k s t h1)). Qed.
Lemma lem4429888 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) (h1 : term13 A K k s t) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t).
Proof. exact (EQ_MP (@lem4426624 A K k s t h1) (@lem4427274 A K k s t h1)). Qed.
Lemma lem4429889 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (t : type1470 A K) : ((@cartesian_product A K k s) = (@cartesian_product A K k t)) = (term23 A K k s t).
Proof. exact (or_elim (@lem4426575 A K k s t) (fun h0 : term13 A K k s t => @lem4429888 A K k s t h0) (fun h0 : term15 A K k s t => @lem4429887 A K k s t h0)). Qed.
Lemma lem4429894 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term472 A K k s.
Proof. exact (fun t : type1470 A K => @lem4429889 A K k s t). Qed.
Lemma lem4429899 {A K : Type'} (k : K -> Prop) : term473 A K k.
Proof. exact (fun s : type1470 A K => @lem4429894 A K k s). Qed.
Lemma lem4429904 {A K : Type'} : term474 A K.
Proof. exact (fun k : K -> Prop => @lem4429899 A K k). Qed.
