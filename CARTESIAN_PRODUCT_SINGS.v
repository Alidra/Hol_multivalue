Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_SINGS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import EXTENSIONAL_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_SING_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem4432590 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4432591 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem4432592 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem4432591 A B f) (@lem4432590 A B f)). Qed.
Lemma lem4432593 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem4432592 A B f g). Qed.
Lemma lem4432594 {A B : Type'} (f : A -> B) (g : A -> B) : (term2 A B f g) = ((f = g) = (term3 A B f g)).
Proof. exact (eq_refl (term2 A B f g)). Qed.
Lemma lem4432596 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4432597 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem4432598 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem4432597 A x) (@lem4432596 A x)). Qed.
Lemma lem4432599 {A : Type'} (x : A) (y : A) : term6 A x y.
Proof. exact (@lem4432598 A x y). Qed.
Lemma lem4432600 {A : Type'} (x : A) (y : A) : (term6 A x y) = ((term7 A x y) = (x = y)).
Proof. exact (eq_refl (term6 A x y)). Qed.
Lemma lem4432612 {_83152 : Type'} : term8 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4432613 {_83152 : Type'} (p : _83152 -> Prop) : term9 _83152 p.
Proof. exact (@lem4432612 _83152 p). Qed.
Lemma lem4432614 {_83152 : Type'} (p : _83152 -> Prop) : (term9 _83152 p) = (term10 _83152 p).
Proof. exact (eq_refl (term9 _83152 p)). Qed.
Lemma lem4432615 {_83152 : Type'} (p : _83152 -> Prop) : term10 _83152 p.
Proof. exact (EQ_MP (@lem4432614 _83152 p) (@lem4432613 _83152 p)). Qed.
Lemma lem4432616 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term11 _83152 p x.
Proof. exact (@lem4432615 _83152 p x). Qed.
Lemma lem4432617 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term11 _83152 p x) = ((term12 _83152 p x) = (p x)).
Proof. exact (eq_refl (term11 _83152 p x)). Qed.
Lemma lem4432626 {_83095 : Type'} : term13 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4432627 {_83095 : Type'} (p : _83095 -> Prop) : term14 _83095 p.
Proof. exact (@lem4432626 _83095 p). Qed.
Lemma lem4432628 {_83095 : Type'} (p : _83095 -> Prop) : (term14 _83095 p) = (term15 _83095 p).
Proof. exact (eq_refl (term14 _83095 p)). Qed.
Lemma lem4432629 {_83095 : Type'} (p : _83095 -> Prop) : term15 _83095 p.
Proof. exact (EQ_MP (@lem4432628 _83095 p) (@lem4432627 _83095 p)). Qed.
Lemma lem4432630 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term16 _83095 p x.
Proof. exact (@lem4432629 _83095 p x). Qed.
Lemma lem4432631 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term16 _83095 p x) = ((term17 _83095 x p) = (p x)).
Proof. exact (eq_refl (term16 _83095 p x)). Qed.
Lemma lem4432640 {A B : Type'} (s : A -> Prop) : term18 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4432641 {A B : Type'} (s : A -> Prop) : (term18 A B s) = ((@EXTENSIONAL A B s) = (term19 A B s)).
Proof. exact (eq_refl (term18 A B s)). Qed.
Lemma lem4432643 {A : Type'} (s : A -> Prop) : term20 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4432644 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (eq_refl (term20 A s)). Qed.
Lemma lem4432645 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (EQ_MP (@lem4432644 A s) (@lem4432643 A s)). Qed.
Lemma lem4432646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term22 A s t.
Proof. exact (@lem4432645 A s t). Qed.
Lemma lem4432647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = ((s = t) = (term23 A s t)).
Proof. exact (eq_refl (term22 A s t)). Qed.
Lemma lem4432649 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4432650 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (eq_refl (term4 A x)). Qed.
Lemma lem4432651 {A : Type'} (x : A) : term5 A x.
Proof. exact (EQ_MP (@lem4432650 A x) (@lem4432649 A x)). Qed.
Lemma lem4432652 {A : Type'} (x : A) (y : A) : term6 A x y.
Proof. exact (@lem4432651 A x y). Qed.
Lemma lem4432653 {A : Type'} (x : A) (y : A) : (term6 A x y) = ((term7 A x y) = (x = y)).
Proof. exact (eq_refl (term6 A x y)). Qed.
Lemma lem4432655 {A K : Type'} (k : K -> Prop) : term24 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4432656 {A K : Type'} (k : K -> Prop) : (term24 A K k) = (term25 A K k).
Proof. exact (eq_refl (term24 A K k)). Qed.
Lemma lem4432657 {A K : Type'} (k : K -> Prop) : term25 A K k.
Proof. exact (EQ_MP (@lem4432656 A K k) (@lem4432655 A K k)). Qed.
Lemma lem4432658 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term26 A K k s.
Proof. exact (@lem4432657 A K k s). Qed.
Lemma lem4432659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term26 A K k s) = ((@cartesian_product A K k s) = (term27 A K k s)).
Proof. exact (eq_refl (term26 A K k s)). Qed.
Lemma lem4432674 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term27 A K k s).
Proof. exact (EQ_MP (@lem4432659 A K k s) (@lem4432658 A K k s)). Qed.
Lemma lem4432675 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term27 A K k s).
Proof. exact (@lem4432674 A K k s). Qed.
Lemma lem4432676 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term28 A K k x) = (term29 A K k x).
Proof. exact (@lem4432675 A K k (term30 A K x)). Qed.
Lemma lem4432690 {A B : Type'} (f : A -> B) (y : A) : (term31 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4432691 {A K : Type'} (f : type1470 A K) (y : K) : (term32 A K f y) = (f y).
Proof. exact (@lem4432690 K (A -> Prop) f y). Qed.
Lemma lem4432692 {A K : Type'} (x : K -> A) (i : K) : (term33 A K x i) = (term34 A K x i).
Proof. exact (@lem4432691 A K (term30 A K x) i). Qed.
Lemma lem4432693 {A K : Type'} (x : K -> A) (i : K) : (term34 A K x i) = (term35 A K x i).
Proof. exact (eq_refl (term34 A K x i)). Qed.
Lemma lem4432694 {A K : Type'} (x : K -> A) : (term36 A K x) = (term30 A K x).
Proof. exact (fun_ext (fun i : K => @lem4432693 A K x i)). Qed.
Lemma lem4432695 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem4432696 {A K : Type'} (x : K -> A) (i : K) : (term33 A K x i) = (term34 A K x i).
Proof. exact (MK_COMB (@lem4432694 A K x) (@lem4432695 K i)). Qed.
Lemma lem4432697 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4432698 {A K : Type'} (x : K -> A) (i : K) : (term37 A K x i) = (term38 A K x i).
Proof. exact (MK_COMB (@lem4432697 A) (@lem4432696 A K x i)). Qed.
Lemma lem4432699 {A K : Type'} (x : K -> A) (i : K) : (term34 A K x i) = (term35 A K x i).
Proof. exact (eq_refl (term34 A K x i)). Qed.
Lemma lem4432700 {A K : Type'} (x : K -> A) (i : K) : ((term33 A K x i) = (term34 A K x i)) = ((term34 A K x i) = (term35 A K x i)).
Proof. exact (MK_COMB (@lem4432698 A K x i) (@lem4432699 A K x i)). Qed.
Lemma lem4432701 {A K : Type'} (x : K -> A) (i : K) : (term34 A K x i) = (term35 A K x i).
Proof. exact (EQ_MP (@lem4432700 A K x i) (@lem4432692 A K x i)). Qed.
Lemma lem4432702 {A K : Type'} (f : K -> A) (i : K) : (term39 A K f i) = (term39 A K f i).
Proof. exact (eq_refl (term39 A K f i)). Qed.
Lemma lem4432703 {A K : Type'} (f : K -> A) (x : K -> A) (i : K) : (term40 A K f x i) = (term41 A K f x i).
Proof. exact (MK_COMB (@lem4432702 A K f i) (@lem4432701 A K x i)). Qed.
Lemma lem4432705 {A : Type'} (x : A) (y : A) : (term7 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4432653 A x y) (@lem4432652 A x y)). Qed.
Lemma lem4432706 {A : Type'} (x : A) (y : A) : (term7 A x y) = (x = y).
Proof. exact (@lem4432705 A x y). Qed.
Lemma lem4432707 {A K : Type'} (f : K -> A) (x : K -> A) (i : K) : (term41 A K f x i) = ((f i) = (x i)).
Proof. exact (@lem4432706 A (f i) (x i)). Qed.
Lemma lem4432710 {A K : Type'} (f : K -> A) (x : K -> A) (i : K) : (term40 A K f x i) = ((f i) = (x i)).
Proof. exact (TRANS (@lem4432703 A K f x i) (@lem4432707 A K f x i)). Qed.
Lemma lem4432711 {K : Type'} (i : K) (k : K -> Prop) : (term42 K i k) = (term42 K i k).
Proof. exact (eq_refl (term42 K i k)). Qed.
Lemma lem4432712 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K -> A) (i : K) : (term43 A K k f x i) = (term44 A K k f x i).
Proof. exact (MK_COMB (@lem4432711 K i k) (@lem4432710 A K f x i)). Qed.
Lemma lem4432715 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K -> A) : (term45 A K k f x) = (term46 A K k f x).
Proof. exact (fun_ext (fun i : K => @lem4432712 A K k f x i)). Qed.
Lemma lem4432716 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4432717 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K -> A) : (term47 A K k f x) = (term48 A K k f x).
Proof. exact (MK_COMB (@lem4432716 K) (@lem4432715 A K k f x)). Qed.
Lemma lem4432722 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term49 A K k f) = (term49 A K k f).
Proof. exact (eq_refl (term49 A K k f)). Qed.
Lemma lem4432723 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K -> A) : (term50 A K k f x) = (term51 A K k f x).
Proof. exact (MK_COMB (@lem4432722 A K k f) (@lem4432717 A K k f x)). Qed.
Lemma lem4432726 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4432727 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (x : K -> A) : (term52 A K GEN_PVAR_140 k f x) = (term53 A K GEN_PVAR_140 k f x).
Proof. exact (MK_COMB (@lem4432726 A K GEN_PVAR_140) (@lem4432723 A K k f x)). Qed.
Lemma lem4432728 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432729 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) (f : K -> A) : (term54 A K GEN_PVAR_140 k x f) = (term55 A K GEN_PVAR_140 k x f).
Proof. exact (MK_COMB (@lem4432727 A K GEN_PVAR_140 k f x) (@lem4432728 A K f)). Qed.
Lemma lem4432730 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) : (term56 A K GEN_PVAR_140 k x) = (term57 A K GEN_PVAR_140 k x).
Proof. exact (fun_ext (fun f : K -> A => @lem4432729 A K GEN_PVAR_140 k x f)). Qed.
Lemma lem4432731 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432732 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) : (term58 A K GEN_PVAR_140 k x) = (term59 A K GEN_PVAR_140 k x).
Proof. exact (MK_COMB (@lem4432731 A K) (@lem4432730 A K GEN_PVAR_140 k x)). Qed.
Lemma lem4432737 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term60 A K k x) = (term61 A K k x).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4432732 A K GEN_PVAR_140 k x)). Qed.
Lemma lem4432738 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432739 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term29 A K k x) = (term62 A K k x).
Proof. exact (MK_COMB (@lem4432738 A K) (@lem4432737 A K k x)). Qed.
Lemma lem4432740 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term28 A K k x) = (term62 A K k x).
Proof. exact (TRANS (@lem4432676 A K k x) (@lem4432739 A K k x)). Qed.
Lemma lem4432741 {A K : Type'} : (@eq ((K -> A) -> Prop)) = (@eq ((K -> A) -> Prop)).
Proof. exact (eq_refl (@eq ((K -> A) -> Prop))). Qed.
Lemma lem4432742 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term63 A K k x) = (term64 A K k x).
Proof. exact (MK_COMB (@lem4432741 A K) (@lem4432740 A K k x)). Qed.
Lemma lem4432743 {A K : Type'} (x : K -> A) : (@INSERT (K -> A) x (@EMPTY (K -> A))) = (@INSERT (K -> A) x (@EMPTY (K -> A))).
Proof. exact (eq_refl (@INSERT (K -> A) x (@EMPTY (K -> A)))). Qed.
Lemma lem4432744 {A K : Type'} (k : K -> Prop) (x : K -> A) : ((term28 A K k x) = (@INSERT (K -> A) x (@EMPTY (K -> A)))) = ((term62 A K k x) = (@INSERT (K -> A) x (@EMPTY (K -> A)))).
Proof. exact (MK_COMB (@lem4432742 A K k x) (@lem4432743 A K x)). Qed.
Lemma lem4432747 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term65 A K k x) = (term65 A K k x).
Proof. exact (eq_refl (term65 A K k x)). Qed.
Lemma lem4432748 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term66 A K k x) = (term67 A K k x).
Proof. exact (MK_COMB (@lem4432747 A K k x) (@lem4432744 A K k x)). Qed.
Lemma lem4432751 {A K : Type'} (k : K -> Prop) : (term68 A K k) = (term69 A K k).
Proof. exact (fun_ext (fun x : K -> A => @lem4432748 A K k x)). Qed.
Lemma lem4432752 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4432753 {A K : Type'} (k : K -> Prop) : (term70 A K k) = (term71 A K k).
Proof. exact (MK_COMB (@lem4432752 A K) (@lem4432751 A K k)). Qed.
Lemma lem4432758 {A K : Type'} : (term72 A K) = (term73 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4432753 A K k)). Qed.
Lemma lem4432759 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4432760 {A K : Type'} : (term74 A K) = (term75 A K).
Proof. exact (MK_COMB (@lem4432759 K) (@lem4432758 A K)). Qed.
Lemma lem4432765 {A K : Type'} : (term75 A K) = (term74 A K).
Proof. exact (SYM (@lem4432760 A K)). Qed.
Lemma lem4432777 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term19 A B s).
Proof. exact (EQ_MP (@lem4432641 A B s) (@lem4432640 A B s)). Qed.
Lemma lem4432778 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term76 A K s).
Proof. exact (@lem4432777 K A s). Qed.
Lemma lem4432779 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term76 A K k).
Proof. exact (@lem4432778 A K k). Qed.
Lemma lem4432794 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4432795 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@EXTENSIONAL K A k x) = (term77 A K k x).
Proof. exact (MK_COMB (@lem4432779 A K k) (@lem4432794 A K x)). Qed.
Lemma lem4432797 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term12 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4432617 _83152 p x) (@lem4432616 _83152 p x)). Qed.
Lemma lem4432798 {A K : Type'} (p : type805 A K) (x : K -> A) : (term78 A K p x) = (p x).
Proof. exact (@lem4432797 (K -> A) p x). Qed.
Lemma lem4432799 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term79 A K k x) = (term80 A K k x).
Proof. exact (@lem4432798 A K (term81 A K k) x). Qed.
Lemma lem4432800 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term80 A K k f) = (term82 A K k f).
Proof. exact (eq_refl (term80 A K k f)). Qed.
Lemma lem4432801 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4432802 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term83 A K GEN_PVAR_139 k f) = (term84 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4432801 A K GEN_PVAR_139) (@lem4432800 A K k f)). Qed.
Lemma lem4432803 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432804 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term85 A K GEN_PVAR_139 k f) = (term86 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4432802 A K GEN_PVAR_139 k f) (@lem4432803 A K f)). Qed.
Lemma lem4432805 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term87 A K GEN_PVAR_139 k) = (term88 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4432804 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4432806 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432807 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term89 A K GEN_PVAR_139 k) = (term90 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4432806 A K) (@lem4432805 A K GEN_PVAR_139 k)). Qed.
Lemma lem4432808 {A K : Type'} (k : K -> Prop) : (term91 A K k) = (term92 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4432807 A K GEN_PVAR_139 k)). Qed.
Lemma lem4432809 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432810 {A K : Type'} (k : K -> Prop) : (term93 A K k) = (term76 A K k).
Proof. exact (MK_COMB (@lem4432809 A K) (@lem4432808 A K k)). Qed.
Lemma lem4432811 {A K : Type'} (x : K -> A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4432812 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term79 A K k x) = (term77 A K k x).
Proof. exact (MK_COMB (@lem4432810 A K k) (@lem4432811 A K x)). Qed.
Lemma lem4432813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432814 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term94 A K k x) = (term95 A K k x).
Proof. exact (MK_COMB (@lem4432813) (@lem4432812 A K k x)). Qed.
Lemma lem4432815 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term80 A K k x) = (term82 A K k x).
Proof. exact (eq_refl (term80 A K k x)). Qed.
Lemma lem4432816 {A K : Type'} (k : K -> Prop) (x : K -> A) : ((term79 A K k x) = (term80 A K k x)) = ((term77 A K k x) = (term82 A K k x)).
Proof. exact (MK_COMB (@lem4432814 A K k x) (@lem4432815 A K k x)). Qed.
Lemma lem4432817 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term77 A K k x) = (term82 A K k x).
Proof. exact (EQ_MP (@lem4432816 A K k x) (@lem4432799 A K k x)). Qed.
Lemma lem4432828 {A K : Type'} (k : K -> Prop) (x : K -> A) : (@EXTENSIONAL K A k x) = (term82 A K k x).
Proof. exact (TRANS (@lem4432795 A K k x) (@lem4432817 A K k x)). Qed.
Lemma lem4432829 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4432830 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term65 A K k x) = (term96 A K k x).
Proof. exact (MK_COMB (@lem4432829) (@lem4432828 A K k x)). Qed.
Lemma lem4432834 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term23 A s t).
Proof. exact (EQ_MP (@lem4432647 A s t) (@lem4432646 A s t)). Qed.
Lemma lem4432835 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term97 A K s t).
Proof. exact (@lem4432834 (K -> A) s t). Qed.
Lemma lem4432836 {A K : Type'} (k : K -> Prop) (x : K -> A) : ((term62 A K k x) = (@INSERT (K -> A) x (@EMPTY (K -> A)))) = (term98 A K k x).
Proof. exact (@lem4432835 A K (term62 A K k x) (@INSERT (K -> A) x (@EMPTY (K -> A)))). Qed.
Lemma lem4432846 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term17 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4432631 _83095 p x) (@lem4432630 _83095 p x)). Qed.
Lemma lem4432847 {A K : Type'} (p : type805 A K) (x : K -> A) : (term99 A K x p) = (p x).
Proof. exact (@lem4432846 (K -> A) p x). Qed.
Lemma lem4432848 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K -> A) : (term100 A K x' k x) = (term101 A K k x x').
Proof. exact (@lem4432847 A K (term102 A K k x) x'). Qed.
Lemma lem4432849 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K -> A) : (term101 A K k x f) = (term51 A K k f x).
Proof. exact (eq_refl (term101 A K k x f)). Qed.
Lemma lem4432850 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4432851 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (x : K -> A) : (term103 A K GEN_PVAR_140 k x f) = (term53 A K GEN_PVAR_140 k f x).
Proof. exact (MK_COMB (@lem4432850 A K GEN_PVAR_140) (@lem4432849 A K k f x)). Qed.
Lemma lem4432852 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432853 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) (f : K -> A) : (term104 A K GEN_PVAR_140 k x f) = (term55 A K GEN_PVAR_140 k x f).
Proof. exact (MK_COMB (@lem4432851 A K GEN_PVAR_140 k f x) (@lem4432852 A K f)). Qed.
Lemma lem4432854 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) : (term105 A K GEN_PVAR_140 k x) = (term57 A K GEN_PVAR_140 k x).
Proof. exact (fun_ext (fun f : K -> A => @lem4432853 A K GEN_PVAR_140 k x f)). Qed.
Lemma lem4432855 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432856 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (x : K -> A) : (term106 A K GEN_PVAR_140 k x) = (term59 A K GEN_PVAR_140 k x).
Proof. exact (MK_COMB (@lem4432855 A K) (@lem4432854 A K GEN_PVAR_140 k x)). Qed.
Lemma lem4432857 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term107 A K k x) = (term61 A K k x).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4432856 A K GEN_PVAR_140 k x)). Qed.
Lemma lem4432858 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432859 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term108 A K k x) = (term62 A K k x).
Proof. exact (MK_COMB (@lem4432858 A K) (@lem4432857 A K k x)). Qed.
Lemma lem4432860 {A K : Type'} (x' : K -> A) : (@IN (K -> A) x') = (@IN (K -> A) x').
Proof. exact (eq_refl (@IN (K -> A) x')). Qed.
Lemma lem4432861 {A K : Type'} (x' : K -> A) (k : K -> Prop) (x : K -> A) : (term100 A K x' k x) = (term109 A K x' k x).
Proof. exact (MK_COMB (@lem4432860 A K x') (@lem4432859 A K k x)). Qed.
Lemma lem4432862 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432863 {A K : Type'} (x' : K -> A) (k : K -> Prop) (x : K -> A) : (term110 A K x' k x) = (term111 A K x' k x).
Proof. exact (MK_COMB (@lem4432862) (@lem4432861 A K x' k x)). Qed.
Lemma lem4432864 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term101 A K k x x') = (term51 A K k x' x).
Proof. exact (eq_refl (term101 A K k x x')). Qed.
Lemma lem4432865 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term100 A K x' k x) = (term101 A K k x x')) = ((term109 A K x' k x) = (term51 A K k x' x)).
Proof. exact (MK_COMB (@lem4432863 A K x' k x) (@lem4432864 A K k x' x)). Qed.
Lemma lem4432866 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term109 A K x' k x) = (term51 A K k x' x).
Proof. exact (EQ_MP (@lem4432865 A K k x' x) (@lem4432848 A K k x x')). Qed.
Lemma lem4432870 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term19 A B s).
Proof. exact (EQ_MP (@lem4432641 A B s) (@lem4432640 A B s)). Qed.
Lemma lem4432871 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term76 A K s).
Proof. exact (@lem4432870 K A s). Qed.
Lemma lem4432872 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term76 A K k).
Proof. exact (@lem4432871 A K k). Qed.
Lemma lem4432887 {A K : Type'} (x' : K -> A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4432888 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (@EXTENSIONAL K A k x') = (term77 A K k x').
Proof. exact (MK_COMB (@lem4432872 A K k) (@lem4432887 A K x')). Qed.
Lemma lem4432890 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term12 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4432617 _83152 p x) (@lem4432616 _83152 p x)). Qed.
Lemma lem4432891 {A K : Type'} (p : type805 A K) (x : K -> A) : (term78 A K p x) = (p x).
Proof. exact (@lem4432890 (K -> A) p x). Qed.
Lemma lem4432892 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term79 A K k x') = (term80 A K k x').
Proof. exact (@lem4432891 A K (term81 A K k) x'). Qed.
Lemma lem4432893 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term80 A K k f) = (term82 A K k f).
Proof. exact (eq_refl (term80 A K k f)). Qed.
Lemma lem4432894 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4432895 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term83 A K GEN_PVAR_139 k f) = (term84 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4432894 A K GEN_PVAR_139) (@lem4432893 A K k f)). Qed.
Lemma lem4432896 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4432897 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term85 A K GEN_PVAR_139 k f) = (term86 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4432895 A K GEN_PVAR_139 k f) (@lem4432896 A K f)). Qed.
Lemma lem4432898 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term87 A K GEN_PVAR_139 k) = (term88 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4432897 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4432899 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4432900 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term89 A K GEN_PVAR_139 k) = (term90 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4432899 A K) (@lem4432898 A K GEN_PVAR_139 k)). Qed.
Lemma lem4432901 {A K : Type'} (k : K -> Prop) : (term91 A K k) = (term92 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4432900 A K GEN_PVAR_139 k)). Qed.
Lemma lem4432902 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4432903 {A K : Type'} (k : K -> Prop) : (term93 A K k) = (term76 A K k).
Proof. exact (MK_COMB (@lem4432902 A K) (@lem4432901 A K k)). Qed.
Lemma lem4432904 {A K : Type'} (x' : K -> A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4432905 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term79 A K k x') = (term77 A K k x').
Proof. exact (MK_COMB (@lem4432903 A K k) (@lem4432904 A K x')). Qed.
Lemma lem4432906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432907 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term94 A K k x') = (term95 A K k x').
Proof. exact (MK_COMB (@lem4432906) (@lem4432905 A K k x')). Qed.
Lemma lem4432908 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term80 A K k x') = (term82 A K k x').
Proof. exact (eq_refl (term80 A K k x')). Qed.
Lemma lem4432909 {A K : Type'} (k : K -> Prop) (x' : K -> A) : ((term79 A K k x') = (term80 A K k x')) = ((term77 A K k x') = (term82 A K k x')).
Proof. exact (MK_COMB (@lem4432907 A K k x') (@lem4432908 A K k x')). Qed.
Lemma lem4432910 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term77 A K k x') = (term82 A K k x').
Proof. exact (EQ_MP (@lem4432909 A K k x') (@lem4432892 A K k x')). Qed.
Lemma lem4432921 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (@EXTENSIONAL K A k x') = (term82 A K k x').
Proof. exact (TRANS (@lem4432888 A K k x') (@lem4432910 A K k x')). Qed.
Lemma lem4432922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4432923 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term49 A K k x') = (term112 A K k x').
Proof. exact (MK_COMB (@lem4432922) (@lem4432921 A K k x')). Qed.
Lemma lem4432934 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term48 A K k x' x) = (term48 A K k x' x).
Proof. exact (eq_refl (term48 A K k x' x)). Qed.
Lemma lem4432935 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term51 A K k x' x) = (term113 A K k x' x).
Proof. exact (MK_COMB (@lem4432923 A K k x') (@lem4432934 A K k x' x)). Qed.
Lemma lem4432938 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term109 A K x' k x) = (term113 A K k x' x).
Proof. exact (TRANS (@lem4432866 A K k x' x) (@lem4432935 A K k x' x)). Qed.
Lemma lem4432939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4432940 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term111 A K x' k x) = (term114 A K k x' x).
Proof. exact (MK_COMB (@lem4432939) (@lem4432938 A K k x' x)). Qed.
Lemma lem4432942 {A : Type'} (x : A) (y : A) : (term7 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4432600 A x y) (@lem4432599 A x y)). Qed.
Lemma lem4432943 {A K : Type'} (x : K -> A) (y : K -> A) : (term115 A K x y) = (x = y).
Proof. exact (@lem4432942 (K -> A) x y). Qed.
Lemma lem4432944 {A K : Type'} (x' : K -> A) (x : K -> A) : (term115 A K x' x) = (x' = x).
Proof. exact (@lem4432943 A K x' x). Qed.
Lemma lem4432949 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term109 A K x' k x) = (term115 A K x' x)) = ((term113 A K k x' x) = (x' = x)).
Proof. exact (MK_COMB (@lem4432940 A K k x' x) (@lem4432944 A K x' x)). Qed.
Lemma lem4432954 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term116 A K k x) = (term117 A K k x).
Proof. exact (fun_ext (fun x' : K -> A => @lem4432949 A K k x' x)). Qed.
Lemma lem4432955 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4432956 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term98 A K k x) = (term118 A K k x).
Proof. exact (MK_COMB (@lem4432955 A K) (@lem4432954 A K k x)). Qed.
Lemma lem4432961 {A K : Type'} (k : K -> Prop) (x : K -> A) : ((term62 A K k x) = (@INSERT (K -> A) x (@EMPTY (K -> A)))) = (term118 A K k x).
Proof. exact (TRANS (@lem4432836 A K k x) (@lem4432956 A K k x)). Qed.
Lemma lem4432962 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term67 A K k x) = (term119 A K k x).
Proof. exact (MK_COMB (@lem4432830 A K k x) (@lem4432961 A K k x)). Qed.
Lemma lem4432965 {A K : Type'} (k : K -> Prop) : (term69 A K k) = (term120 A K k).
Proof. exact (fun_ext (fun x : K -> A => @lem4432962 A K k x)). Qed.
Lemma lem4432966 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4432967 {A K : Type'} (k : K -> Prop) : (term71 A K k) = (term121 A K k).
Proof. exact (MK_COMB (@lem4432966 A K) (@lem4432965 A K k)). Qed.
Lemma lem4432972 {A K : Type'} : (term73 A K) = (term122 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4432967 A K k)). Qed.
Lemma lem4432973 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4432974 {A K : Type'} : (term75 A K) = (term123 A K).
Proof. exact (MK_COMB (@lem4432973 K) (@lem4432972 A K)). Qed.
Lemma lem4432979 {A K : Type'} : (term123 A K) = (term75 A K).
Proof. exact (SYM (@lem4432974 A K)). Qed.
Lemma lem4433033 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term3 A B f g).
Proof. exact (EQ_MP (@lem4432594 A B f g) (@lem4432593 A B f g)). Qed.
Lemma lem4433034 {A K : Type'} (f : K -> A) (g : K -> A) : (f = g) = (term124 A K f g).
Proof. exact (@lem4433033 K A f g). Qed.
Lemma lem4433035 {A K : Type'} (x' : K -> A) (x : K -> A) : (x' = x) = (term124 A K x' x).
Proof. exact (@lem4433034 A K x' x). Qed.
Lemma lem4433044 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term114 A K k x' x) = (term114 A K k x' x).
Proof. exact (eq_refl (term114 A K k x' x)). Qed.
Lemma lem4433045 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term113 A K k x' x) = (x' = x)) = ((term113 A K k x' x) = (term124 A K x' x)).
Proof. exact (MK_COMB (@lem4433044 A K k x' x) (@lem4433035 A K x' x)). Qed.
Lemma lem4433050 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term117 A K k x) = (term125 A K k x).
Proof. exact (fun_ext (fun x' : K -> A => @lem4433045 A K k x' x)). Qed.
Lemma lem4433051 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4433052 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term118 A K k x) = (term126 A K k x).
Proof. exact (MK_COMB (@lem4433051 A K) (@lem4433050 A K k x)). Qed.
Lemma lem4433057 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term96 A K k x) = (term96 A K k x).
Proof. exact (eq_refl (term96 A K k x)). Qed.
Lemma lem4433058 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term119 A K k x) = (term127 A K k x).
Proof. exact (MK_COMB (@lem4433057 A K k x) (@lem4433052 A K k x)). Qed.
Lemma lem4433061 {A K : Type'} (k : K -> Prop) : (term120 A K k) = (term128 A K k).
Proof. exact (fun_ext (fun x : K -> A => @lem4433058 A K k x)). Qed.
Lemma lem4433062 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4433063 {A K : Type'} (k : K -> Prop) : (term121 A K k) = (term129 A K k).
Proof. exact (MK_COMB (@lem4433062 A K) (@lem4433061 A K k)). Qed.
Lemma lem4433068 {A K : Type'} : (term122 A K) = (term130 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4433063 A K k)). Qed.
Lemma lem4433069 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4433070 {A K : Type'} : (term123 A K) = (term131 A K).
Proof. exact (MK_COMB (@lem4433069 K) (@lem4433068 A K)). Qed.
Lemma lem4433075 {A K : Type'} : (term131 A K) = (term123 A K).
Proof. exact (SYM (@lem4433070 A K)). Qed.
Lemma lem4433077 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4433078 {A K : Type'} : (term131 A K) = (term133 A K).
Proof. exact (@lem4433077 (term131 A K)). Qed.
Lemma lem4433079 {A K : Type'} : (term133 A K) = (term131 A K).
Proof. exact (SYM (@lem4433078 A K)). Qed.
Lemma lem4433080 {A K : Type'} (h1 : term134 A K) : term134 A K.
Proof. exact (h1). Qed.
Lemma lem4433083 {A K : Type'} (h1 : term133 A K) : term133 A K.
Proof. exact (h1). Qed.
Lemma lem4433084 {A K : Type'} : term135 A K.
Proof. exact (fun h0 : term133 A K => @lem4433083 A K h0). Qed.
Lemma lem4433085 {A K : Type'} (h1 : term135 A K) : term135 A K.
Proof. exact (h1). Qed.
Lemma lem4433086 {A K : Type'} (h1 : term133 A K) : term133 A K.
Proof. exact (h1). Qed.
Lemma lem4433087 {A K : Type'} (h1 : term133 A K) (h2 : term135 A K) : term133 A K.
Proof. exact (@lem4433085 A K h2 (@lem4433086 A K h1)). Qed.
Lemma lem4433088 {A K : Type'} (h1 : term133 A K) : term136 A K.
Proof. exact (fun h0 : term135 A K => @lem4433087 A K h1 h0). Qed.
Lemma lem4433089 {A K : Type'} (h1 : term135 A K) : term135 A K.
Proof. exact (h1). Qed.
Lemma lem4433090 {A K : Type'} (h1 : term133 A K) (h2 : term135 A K) : term133 A K.
Proof. exact (@lem4433088 A K h1 (@lem4433089 A K h2)). Qed.
Lemma lem4433091 {A K : Type'} (h1 : term135 A K) : term135 A K.
Proof. exact (fun h0 : term133 A K => @lem4433090 A K h0 h1). Qed.
Lemma lem4433092 {A K : Type'} : term137 A K.
Proof. exact (fun h0 : term135 A K => @lem4433091 A K h0). Qed.
Lemma lem4433095 {A K : Type'} : term135 A K.
Proof. exact (@lem4433092 A K (@lem4433084 A K)). Qed.
Lemma lem4433096 {A K : Type'} : term135 A K.
Proof. exact (@lem4433095 A K). Qed.
Lemma lem4433098 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4433099 {A K : Type'} : (term133 A K) = (term138 A K).
Proof. exact (@lem4433098 (term134 A K)). Qed.
Lemma lem4433101 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4433102 {A K : Type'} : (term138 A K) = (term131 A K).
Proof. exact (@lem4433101 (term131 A K)). Qed.
Lemma lem4433145 {A K : Type'} : (term133 A K) = (term131 A K).
Proof. exact (TRANS (@lem4433099 A K) (@lem4433102 A K)). Qed.
Lemma lem4433146 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : ((x' x'') = (x x'')) = ((x' x'') = (x x'')).
Proof. exact (eq_refl ((x' x'') = (x x''))). Qed.
Lemma lem4433147 {A K : Type'} (x' : K -> A) (x : K -> A) : (term140 A K x' x) = (term140 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433146 A K x' x x'')). Qed.
Lemma lem4433148 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433149 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (MK_COMB (@lem4433148 K) (@lem4433147 A K x' x)). Qed.
Lemma lem4433154 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term44 A K k x' x i) = (term44 A K k x' x i).
Proof. exact (eq_refl (term44 A K k x' x i)). Qed.
Lemma lem4433155 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term46 A K k x' x) = (term46 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433154 A K k x' x i)). Qed.
Lemma lem4433156 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433157 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term48 A K k x' x) = (term48 A K k x' x).
Proof. exact (MK_COMB (@lem4433156 K) (@lem4433155 A K k x' x)). Qed.
Lemma lem4433164 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term141 A K k x' x) = (term141 A K k x' x).
Proof. exact (eq_refl (term141 A K k x' x)). Qed.
Lemma lem4433165 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term142 A K k x') = (term142 A K k x').
Proof. exact (fun_ext (fun x : K => @lem4433164 A K k x' x)). Qed.
Lemma lem4433166 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433167 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term82 A K k x') = (term82 A K k x').
Proof. exact (MK_COMB (@lem4433166 K) (@lem4433165 A K k x')). Qed.
Lemma lem4433168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433169 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term112 A K k x') = (term112 A K k x').
Proof. exact (MK_COMB (@lem4433168) (@lem4433167 A K k x')). Qed.
Lemma lem4433170 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term113 A K k x' x) = (term113 A K k x' x).
Proof. exact (MK_COMB (@lem4433169 A K k x') (@lem4433157 A K k x' x)). Qed.
Lemma lem4433171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433172 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term114 A K k x' x) = (term114 A K k x' x).
Proof. exact (MK_COMB (@lem4433171) (@lem4433170 A K k x' x)). Qed.
Lemma lem4433173 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term113 A K k x' x) = (term124 A K x' x)) = ((term113 A K k x' x) = (term124 A K x' x)).
Proof. exact (MK_COMB (@lem4433172 A K k x' x) (@lem4433149 A K x' x)). Qed.
Lemma lem4433174 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term125 A K k x) = (term125 A K k x).
Proof. exact (fun_ext (fun x' : K -> A => @lem4433173 A K k x' x)). Qed.
Lemma lem4433175 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4433176 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term126 A K k x) = (term126 A K k x).
Proof. exact (MK_COMB (@lem4433175 A K) (@lem4433174 A K k x)). Qed.
Lemma lem4433183 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term141 A K k x x') = (term141 A K k x x').
Proof. exact (eq_refl (term141 A K k x x')). Qed.
Lemma lem4433184 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term142 A K k x) = (term142 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4433183 A K k x x')). Qed.
Lemma lem4433185 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433186 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term82 A K k x) = (term82 A K k x).
Proof. exact (MK_COMB (@lem4433185 K) (@lem4433184 A K k x)). Qed.
Lemma lem4433187 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4433188 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term96 A K k x) = (term96 A K k x).
Proof. exact (MK_COMB (@lem4433187) (@lem4433186 A K k x)). Qed.
Lemma lem4433189 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term127 A K k x) = (term127 A K k x).
Proof. exact (MK_COMB (@lem4433188 A K k x) (@lem4433176 A K k x)). Qed.
Lemma lem4433190 {A K : Type'} (k : K -> Prop) : (term128 A K k) = (term128 A K k).
Proof. exact (fun_ext (fun x : K -> A => @lem4433189 A K k x)). Qed.
Lemma lem4433191 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4433192 {A K : Type'} (k : K -> Prop) : (term129 A K k) = (term129 A K k).
Proof. exact (MK_COMB (@lem4433191 A K) (@lem4433190 A K k)). Qed.
Lemma lem4433193 {A K : Type'} : (term130 A K) = (term130 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4433192 A K k)). Qed.
Lemma lem4433194 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4433195 {A K : Type'} : (term131 A K) = (term131 A K).
Proof. exact (MK_COMB (@lem4433194 K) (@lem4433193 A K)). Qed.
Lemma lem4433250 {A K : Type'} : (term133 A K) = (term131 A K).
Proof. exact (TRANS (@lem4433145 A K) (@lem4433195 A K)). Qed.
Lemma lem4433251 {A K : Type'} : (term131 A K) = (term133 A K).
Proof. exact (SYM (@lem4433250 A K)). Qed.
Lemma lem4433252 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term82 A K k x.
Proof. exact (h1). Qed.
Lemma lem4433254 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4433255 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term113 A K k x' x) = (term124 A K x' x)) = (term143 A K k x' x).
Proof. exact (@lem4433254 ((term113 A K k x' x) = (term124 A K x' x))). Qed.
Lemma lem4433256 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term143 A K k x' x) = ((term113 A K k x' x) = (term124 A K x' x)).
Proof. exact (SYM (@lem4433255 A K k x' x)). Qed.
Lemma lem4433257 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (h1 : term144 A K k x' x) : term144 A K k x' x.
Proof. exact (h1). Qed.
Lemma lem4433260 {K : Type'} (x : K) (k : K -> Prop) : (term145 K x k) = (@IN K x k).
Proof. exact (@lem16933 (@IN K x k)). Qed.
Lemma lem4433261 {A K : Type'} (x : K -> A) (x' : K) : ((x x') = (@ARB A)) = ((x x') = (@ARB A)).
Proof. exact (eq_refl ((x x') = (@ARB A))). Qed.
Lemma lem4433262 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433263 {K : Type'} (x : K) (k : K -> Prop) : (term146 K x k) = (term147 K x k).
Proof. exact (MK_COMB (@lem4433262) (@lem4433260 K x k)). Qed.
Lemma lem4433264 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term148 A K k x x') = (term149 A K k x x').
Proof. exact (MK_COMB (@lem4433263 K x' k) (@lem4433261 A K x x')). Qed.
Lemma lem4433265 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term141 A K k x x') = (term148 A K k x x').
Proof. exact (@lem17265 (term150 K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4433266 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term141 A K k x x') = (term149 A K k x x').
Proof. exact (TRANS (@lem4433265 A K k x x') (@lem4433264 A K k x x')). Qed.
Lemma lem4433267 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term142 A K k x) = (term151 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4433266 A K k x x')). Qed.
Lemma lem4433268 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433321 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term82 A K k x) = (term152 A K k x).
Proof. exact (MK_COMB (@lem4433268 K) (@lem4433267 A K k x)). Qed.
Lemma lem4433322 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term152 A K k x.
Proof. exact (EQ_MP (@lem4433321 A K k x) (@lem4433252 A K k x h1)). Qed.
Lemma lem4433326 {K : Type'} (x : K) (k : K -> Prop) : (term145 K x k) = (@IN K x k).
Proof. exact (@lem16933 (@IN K x k)). Qed.
Lemma lem4433328 {A K : Type'} (x' : K -> A) (x : K) : ((x' x) = (@ARB A)) = ((x' x) = (@ARB A)).
Proof. exact (eq_refl ((x' x) = (@ARB A))). Qed.
Lemma lem4433333 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term153 A K k x' x) = (term154 A K k x' x).
Proof. exact (@lem17362 (term150 K x k) ((x' x) = (@ARB A))). Qed.
Lemma lem4433334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433335 {K : Type'} (x : K) (k : K -> Prop) : (term146 K x k) = (term147 K x k).
Proof. exact (MK_COMB (@lem4433334) (@lem4433326 K x k)). Qed.
Lemma lem4433336 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term148 A K k x' x) = (term149 A K k x' x).
Proof. exact (MK_COMB (@lem4433335 K x k) (@lem4433328 A K x' x)). Qed.
Lemma lem4433337 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term141 A K k x' x) = (term148 A K k x' x).
Proof. exact (@lem17265 (term150 K x k) ((x' x) = (@ARB A))). Qed.
Lemma lem4433338 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term141 A K k x' x) = (term149 A K k x' x).
Proof. exact (TRANS (@lem4433337 A K k x' x) (@lem4433336 A K k x' x)). Qed.
Lemma lem4433339 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4433340 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term157 A K k x') = (term158 A K k x').
Proof. exact (@lem4433339 K (term142 A K k x')). Qed.
Lemma lem4433341 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term159 A K k x' x) = (term141 A K k x' x).
Proof. exact (eq_refl (term159 A K k x' x)). Qed.
Lemma lem4433342 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4433343 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term160 A K k x' x) = (term153 A K k x' x).
Proof. exact (MK_COMB (@lem4433342) (@lem4433341 A K k x' x)). Qed.
Lemma lem4433344 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term160 A K k x' x) = (term154 A K k x' x).
Proof. exact (TRANS (@lem4433343 A K k x' x) (@lem4433333 A K k x' x)). Qed.
Lemma lem4433345 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term161 A K k x') = (term162 A K k x').
Proof. exact (fun_ext (fun x : K => @lem4433344 A K k x' x)). Qed.
Lemma lem4433346 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433347 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term158 A K k x') = (term163 A K k x').
Proof. exact (MK_COMB (@lem4433346 K) (@lem4433345 A K k x')). Qed.
Lemma lem4433348 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term157 A K k x') = (term163 A K k x').
Proof. exact (TRANS (@lem4433340 A K k x') (@lem4433347 A K k x')). Qed.
Lemma lem4433349 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term142 A K k x') = (term151 A K k x').
Proof. exact (fun_ext (fun x : K => @lem4433338 A K k x' x)). Qed.
Lemma lem4433350 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433351 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term82 A K k x') = (term152 A K k x').
Proof. exact (MK_COMB (@lem4433350 K) (@lem4433349 A K k x')). Qed.
Lemma lem4433360 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term164 A K k x' x i) = (term165 A K k x' x i).
Proof. exact (@lem17362 (@IN K i k) ((x' i) = (x i))). Qed.
Lemma lem4433365 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term44 A K k x' x i) = (term166 A K k x' x i).
Proof. exact (@lem17265 (@IN K i k) ((x' i) = (x i))). Qed.
Lemma lem4433366 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4433367 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term167 A K k x' x) = (term168 A K k x' x).
Proof. exact (@lem4433366 K (term46 A K k x' x)). Qed.
Lemma lem4433368 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term169 A K k x' x i) = (term44 A K k x' x i).
Proof. exact (eq_refl (term169 A K k x' x i)). Qed.
Lemma lem4433369 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4433370 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term170 A K k x' x i) = (term164 A K k x' x i).
Proof. exact (MK_COMB (@lem4433369) (@lem4433368 A K k x' x i)). Qed.
Lemma lem4433371 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term170 A K k x' x i) = (term165 A K k x' x i).
Proof. exact (TRANS (@lem4433370 A K k x' x i) (@lem4433360 A K k x' x i)). Qed.
Lemma lem4433372 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term171 A K k x' x) = (term172 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433371 A K k x' x i)). Qed.
Lemma lem4433373 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433374 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term168 A K k x' x) = (term173 A K k x' x).
Proof. exact (MK_COMB (@lem4433373 K) (@lem4433372 A K k x' x)). Qed.
Lemma lem4433375 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term167 A K k x' x) = (term173 A K k x' x).
Proof. exact (TRANS (@lem4433367 A K k x' x) (@lem4433374 A K k x' x)). Qed.
Lemma lem4433376 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term46 A K k x' x) = (term174 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433365 A K k x' x i)). Qed.
Lemma lem4433377 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433378 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term48 A K k x' x) = (term175 A K k x' x).
Proof. exact (MK_COMB (@lem4433377 K) (@lem4433376 A K k x' x)). Qed.
Lemma lem4433379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433380 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term176 A K k x') = (term177 A K k x').
Proof. exact (MK_COMB (@lem4433379) (@lem4433348 A K k x')). Qed.
Lemma lem4433381 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term178 A K k x' x) = (term179 A K k x' x).
Proof. exact (MK_COMB (@lem4433380 A K k x') (@lem4433375 A K k x' x)). Qed.
Lemma lem4433382 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term180 A K k x' x) = (term178 A K k x' x).
Proof. exact (@lem17045 (term82 A K k x') (term48 A K k x' x)). Qed.
Lemma lem4433383 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term180 A K k x' x) = (term179 A K k x' x).
Proof. exact (TRANS (@lem4433382 A K k x' x) (@lem4433381 A K k x' x)). Qed.
Lemma lem4433384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433385 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term112 A K k x') = (term181 A K k x').
Proof. exact (MK_COMB (@lem4433384) (@lem4433351 A K k x')). Qed.
Lemma lem4433386 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term113 A K k x' x) = (term182 A K k x' x).
Proof. exact (MK_COMB (@lem4433385 A K k x') (@lem4433378 A K k x' x)). Qed.
Lemma lem4433388 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : ((x' x'') = (x x'')) = ((x' x'') = (x x'')).
Proof. exact (eq_refl ((x' x'') = (x x''))). Qed.
Lemma lem4433389 {K : Type'} (P : K -> Prop) : (term155 K P) = (term156 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4433390 {A K : Type'} (x' : K -> A) (x : K -> A) : (term183 A K x' x) = (term184 A K x' x).
Proof. exact (@lem4433389 K (term140 A K x' x)). Qed.
Lemma lem4433391 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : (term185 A K x' x x'') = ((x' x'') = (x x'')).
Proof. exact (eq_refl (term185 A K x' x x'')). Qed.
Lemma lem4433392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4433394 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : (term186 A K x' x x'') = (term187 A K x' x x'').
Proof. exact (MK_COMB (@lem4433392) (@lem4433391 A K x' x x'')). Qed.
Lemma lem4433395 {A K : Type'} (x' : K -> A) (x : K -> A) : (term188 A K x' x) = (term189 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433394 A K x' x x'')). Qed.
Lemma lem4433396 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433397 {A K : Type'} (x' : K -> A) (x : K -> A) : (term184 A K x' x) = (term190 A K x' x).
Proof. exact (MK_COMB (@lem4433396 K) (@lem4433395 A K x' x)). Qed.
Lemma lem4433398 {A K : Type'} (x' : K -> A) (x : K -> A) : (term183 A K x' x) = (term190 A K x' x).
Proof. exact (TRANS (@lem4433390 A K x' x) (@lem4433397 A K x' x)). Qed.
Lemma lem4433399 {A K : Type'} (x' : K -> A) (x : K -> A) : (term140 A K x' x) = (term140 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433388 A K x' x x'')). Qed.
Lemma lem4433400 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433401 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (MK_COMB (@lem4433400 K) (@lem4433399 A K x' x)). Qed.
Lemma lem4433402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433403 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term191 A K k x' x) = (term192 A K k x' x).
Proof. exact (MK_COMB (@lem4433402) (@lem4433383 A K k x' x)). Qed.
Lemma lem4433404 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term193 A K k x' x) = (term194 A K k x' x).
Proof. exact (MK_COMB (@lem4433403 A K k x' x) (@lem4433401 A K x' x)). Qed.
Lemma lem4433405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433406 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term195 A K k x' x) = (term196 A K k x' x).
Proof. exact (MK_COMB (@lem4433405) (@lem4433386 A K k x' x)). Qed.
Lemma lem4433407 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term197 A K k x' x) = (term198 A K k x' x).
Proof. exact (MK_COMB (@lem4433406 A K k x' x) (@lem4433398 A K x' x)). Qed.
Lemma lem4433408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433409 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term199 A K k x' x) = (term200 A K k x' x).
Proof. exact (MK_COMB (@lem4433408) (@lem4433407 A K k x' x)). Qed.
Lemma lem4433410 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term201 A K k x' x) = (term202 A K k x' x).
Proof. exact (MK_COMB (@lem4433409 A K k x' x) (@lem4433404 A K k x' x)). Qed.
Lemma lem4433411 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term144 A K k x' x) = (term201 A K k x' x).
Proof. exact (@lem17646 (term113 A K k x' x) (term124 A K x' x)). Qed.
Lemma lem4433412 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term144 A K k x' x) = (term202 A K k x' x).
Proof. exact (TRANS (@lem4433411 A K k x' x) (@lem4433410 A K k x' x)). Qed.
Lemma lem4433615 {A : Type'} (P : Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4433616 {K : Type'} (P : Prop) (Q : K -> Prop) : (term203 K P Q) = (term204 K P Q).
Proof. exact (@lem4433615 K P Q). Qed.
Lemma lem4433617 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term205 A K k x' x) = (term206 A K k x' x).
Proof. exact (@lem4433616 K (term182 A K k x' x) (term189 A K x' x)). Qed.
Lemma lem4433618 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : (term207 A K x' x x'') = (term187 A K x' x x'').
Proof. exact (eq_refl (term207 A K x' x x'')). Qed.
Lemma lem4433619 {A K : Type'} (x' : K -> A) (x : K -> A) : (term208 A K x' x) = (term189 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433618 A K x' x x'')). Qed.
Lemma lem4433620 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433621 {A K : Type'} (x' : K -> A) (x : K -> A) : (term209 A K x' x) = (term190 A K x' x).
Proof. exact (MK_COMB (@lem4433620 K) (@lem4433619 A K x' x)). Qed.
Lemma lem4433622 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term196 A K k x' x) = (term196 A K k x' x).
Proof. exact (eq_refl (term196 A K k x' x)). Qed.
Lemma lem4433623 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term205 A K k x' x) = (term198 A K k x' x).
Proof. exact (MK_COMB (@lem4433622 A K k x' x) (@lem4433621 A K x' x)). Qed.
Lemma lem4433624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433625 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term210 A K k x' x) = (term211 A K k x' x).
Proof. exact (MK_COMB (@lem4433624) (@lem4433623 A K k x' x)). Qed.
Lemma lem4433626 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : (term207 A K x' x x'') = (term187 A K x' x x'').
Proof. exact (eq_refl (term207 A K x' x x'')). Qed.
Lemma lem4433627 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term196 A K k x' x) = (term196 A K k x' x).
Proof. exact (eq_refl (term196 A K k x' x)). Qed.
Lemma lem4433628 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (x'' : K) : (term212 A K k x' x x'') = (term213 A K k x' x x'').
Proof. exact (MK_COMB (@lem4433627 A K k x' x) (@lem4433626 A K x' x x'')). Qed.
Lemma lem4433629 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term214 A K k x' x) = (term215 A K k x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433628 A K k x' x x'')). Qed.
Lemma lem4433630 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433631 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term206 A K k x' x) = (term216 A K k x' x).
Proof. exact (MK_COMB (@lem4433630 K) (@lem4433629 A K k x' x)). Qed.
Lemma lem4433632 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term205 A K k x' x) = (term206 A K k x' x)) = ((term198 A K k x' x) = (term216 A K k x' x)).
Proof. exact (MK_COMB (@lem4433625 A K k x' x) (@lem4433631 A K k x' x)). Qed.
Lemma lem4433633 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term198 A K k x' x) = (term216 A K k x' x).
Proof. exact (EQ_MP (@lem4433632 A K k x' x) (@lem4433617 A K k x' x)). Qed.
Lemma lem4433634 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433635 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term200 A K k x' x) = (term217 A K k x' x).
Proof. exact (MK_COMB (@lem4433634) (@lem4433633 A K k x' x)). Qed.
Lemma lem4433637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4433638 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term218 K P Q) = (term219 K P Q).
Proof. exact (@lem4433637 K P Q). Qed.
Lemma lem4433639 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term220 A K k x' x) = (term221 A K k x' x).
Proof. exact (@lem4433638 K (term162 A K k x') (term172 A K k x' x)). Qed.
Lemma lem4433640 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) : (term222 A K k x' i) = (term154 A K k x' i).
Proof. exact (eq_refl (term222 A K k x' i)). Qed.
Lemma lem4433641 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term223 A K k x') = (term162 A K k x').
Proof. exact (fun_ext (fun i : K => @lem4433640 A K k x' i)). Qed.
Lemma lem4433642 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433643 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term224 A K k x') = (term163 A K k x').
Proof. exact (MK_COMB (@lem4433642 K) (@lem4433641 A K k x')). Qed.
Lemma lem4433644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433645 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term225 A K k x') = (term177 A K k x').
Proof. exact (MK_COMB (@lem4433644) (@lem4433643 A K k x')). Qed.
Lemma lem4433646 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term226 A K k x' x i) = (term165 A K k x' x i).
Proof. exact (eq_refl (term226 A K k x' x i)). Qed.
Lemma lem4433647 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term227 A K k x' x) = (term172 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433646 A K k x' x i)). Qed.
Lemma lem4433648 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433649 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term228 A K k x' x) = (term173 A K k x' x).
Proof. exact (MK_COMB (@lem4433648 K) (@lem4433647 A K k x' x)). Qed.
Lemma lem4433650 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term220 A K k x' x) = (term179 A K k x' x).
Proof. exact (MK_COMB (@lem4433645 A K k x') (@lem4433649 A K k x' x)). Qed.
Lemma lem4433651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433652 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term229 A K k x' x) = (term230 A K k x' x).
Proof. exact (MK_COMB (@lem4433651) (@lem4433650 A K k x' x)). Qed.
Lemma lem4433653 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) : (term222 A K k x' i) = (term154 A K k x' i).
Proof. exact (eq_refl (term222 A K k x' i)). Qed.
Lemma lem4433654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433655 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) : (term231 A K k x' i) = (term232 A K k x' i).
Proof. exact (MK_COMB (@lem4433654) (@lem4433653 A K k x' i)). Qed.
Lemma lem4433656 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term226 A K k x' x i) = (term165 A K k x' x i).
Proof. exact (eq_refl (term226 A K k x' x i)). Qed.
Lemma lem4433657 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term233 A K k x' x i) = (term234 A K k x' x i).
Proof. exact (MK_COMB (@lem4433655 A K k x' i) (@lem4433656 A K k x' x i)). Qed.
Lemma lem4433658 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term235 A K k x' x) = (term236 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433657 A K k x' x i)). Qed.
Lemma lem4433659 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433660 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term221 A K k x' x) = (term237 A K k x' x).
Proof. exact (MK_COMB (@lem4433659 K) (@lem4433658 A K k x' x)). Qed.
Lemma lem4433661 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term220 A K k x' x) = (term221 A K k x' x)) = ((term179 A K k x' x) = (term237 A K k x' x)).
Proof. exact (MK_COMB (@lem4433652 A K k x' x) (@lem4433660 A K k x' x)). Qed.
Lemma lem4433662 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term179 A K k x' x) = (term237 A K k x' x).
Proof. exact (EQ_MP (@lem4433661 A K k x' x) (@lem4433639 A K k x' x)). Qed.
Lemma lem4433665 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term238 A K k x' x) = (term238 A K k x' x).
Proof. exact (eq_refl (term238 A K k x' x)). Qed.
Lemma lem4433666 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term238 A K k x' x) = ((term179 A K k x' x) = (term237 A K k x' x)).
Proof. exact (eq_refl (term238 A K k x' x)). Qed.
Lemma lem4433667 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term239 A K k x' x) = (term239 A K k x' x).
Proof. exact (eq_refl (term239 A K k x' x)). Qed.
Lemma lem4433668 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term238 A K k x' x) = (term238 A K k x' x)) = ((term238 A K k x' x) = ((term179 A K k x' x) = (term237 A K k x' x))).
Proof. exact (MK_COMB (@lem4433667 A K k x' x) (@lem4433666 A K k x' x)). Qed.
Lemma lem4433669 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term238 A K k x' x) = ((term179 A K k x' x) = (term237 A K k x' x)).
Proof. exact (eq_refl (term238 A K k x' x)). Qed.
Lemma lem4433670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433671 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term239 A K k x' x) = (term240 A K k x' x).
Proof. exact (MK_COMB (@lem4433670) (@lem4433669 A K k x' x)). Qed.
Lemma lem4433672 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term179 A K k x' x) = (term237 A K k x' x)) = ((term179 A K k x' x) = (term237 A K k x' x)).
Proof. exact (eq_refl ((term179 A K k x' x) = (term237 A K k x' x))). Qed.
Lemma lem4433673 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term238 A K k x' x) = ((term179 A K k x' x) = (term237 A K k x' x))) = (((term179 A K k x' x) = (term237 A K k x' x)) = ((term179 A K k x' x) = (term237 A K k x' x))).
Proof. exact (MK_COMB (@lem4433671 A K k x' x) (@lem4433672 A K k x' x)). Qed.
Lemma lem4433674 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term238 A K k x' x) = (term238 A K k x' x)) = (((term179 A K k x' x) = (term237 A K k x' x)) = ((term179 A K k x' x) = (term237 A K k x' x))).
Proof. exact (TRANS (@lem4433668 A K k x' x) (@lem4433673 A K k x' x)). Qed.
Lemma lem4433675 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term179 A K k x' x) = (term237 A K k x' x)) = ((term179 A K k x' x) = (term237 A K k x' x)).
Proof. exact (EQ_MP (@lem4433674 A K k x' x) (@lem4433665 A K k x' x)). Qed.
Lemma lem4433676 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term179 A K k x' x) = (term237 A K k x' x).
Proof. exact (EQ_MP (@lem4433675 A K k x' x) (@lem4433662 A K k x' x)). Qed.
Lemma lem4433677 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433678 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term192 A K k x' x) = (term241 A K k x' x).
Proof. exact (MK_COMB (@lem4433677) (@lem4433676 A K k x' x)). Qed.
Lemma lem4433679 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (eq_refl (term124 A K x' x)). Qed.
Lemma lem4433680 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term194 A K k x' x) = (term242 A K k x' x).
Proof. exact (MK_COMB (@lem4433678 A K k x' x) (@lem4433679 A K x' x)). Qed.
Lemma lem4433682 {A : Type'} (P : A -> Prop) (Q : Prop) : (term243 A P Q) = (term244 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4433683 {K : Type'} (P : K -> Prop) (Q : Prop) : (term243 K P Q) = (term244 K P Q).
Proof. exact (@lem4433682 K P Q). Qed.
Lemma lem4433684 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term245 A K k x' x) = (term246 A K k x' x).
Proof. exact (@lem4433683 K (term236 A K k x' x) (term124 A K x' x)). Qed.
Lemma lem4433685 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term247 A K k x' x i) = (term234 A K k x' x i).
Proof. exact (eq_refl (term247 A K k x' x i)). Qed.
Lemma lem4433686 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term248 A K k x' x) = (term236 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433685 A K k x' x i)). Qed.
Lemma lem4433687 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433688 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term249 A K k x' x) = (term237 A K k x' x).
Proof. exact (MK_COMB (@lem4433687 K) (@lem4433686 A K k x' x)). Qed.
Lemma lem4433689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433690 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term250 A K k x' x) = (term241 A K k x' x).
Proof. exact (MK_COMB (@lem4433689) (@lem4433688 A K k x' x)). Qed.
Lemma lem4433691 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (eq_refl (term124 A K x' x)). Qed.
Lemma lem4433692 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term245 A K k x' x) = (term242 A K k x' x).
Proof. exact (MK_COMB (@lem4433690 A K k x' x) (@lem4433691 A K x' x)). Qed.
Lemma lem4433693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433694 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term251 A K k x' x) = (term252 A K k x' x).
Proof. exact (MK_COMB (@lem4433693) (@lem4433692 A K k x' x)). Qed.
Lemma lem4433695 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term247 A K k x' x i) = (term234 A K k x' x i).
Proof. exact (eq_refl (term247 A K k x' x i)). Qed.
Lemma lem4433696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433697 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term253 A K k x' x i) = (term254 A K k x' x i).
Proof. exact (MK_COMB (@lem4433696) (@lem4433695 A K k x' x i)). Qed.
Lemma lem4433698 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (eq_refl (term124 A K x' x)). Qed.
Lemma lem4433699 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term255 A K k i x' x) = (term256 A K k i x' x).
Proof. exact (MK_COMB (@lem4433697 A K k x' x i) (@lem4433698 A K x' x)). Qed.
Lemma lem4433700 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term257 A K k x' x) = (term258 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433699 A K k i x' x)). Qed.
Lemma lem4433701 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433702 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term246 A K k x' x) = (term259 A K k x' x).
Proof. exact (MK_COMB (@lem4433701 K) (@lem4433700 A K k x' x)). Qed.
Lemma lem4433703 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term245 A K k x' x) = (term246 A K k x' x)) = ((term242 A K k x' x) = (term259 A K k x' x)).
Proof. exact (MK_COMB (@lem4433694 A K k x' x) (@lem4433702 A K k x' x)). Qed.
Lemma lem4433704 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term242 A K k x' x) = (term259 A K k x' x).
Proof. exact (EQ_MP (@lem4433703 A K k x' x) (@lem4433684 A K k x' x)). Qed.
Lemma lem4433705 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term194 A K k x' x) = (term259 A K k x' x).
Proof. exact (TRANS (@lem4433680 A K k x' x) (@lem4433704 A K k x' x)). Qed.
Lemma lem4433706 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term202 A K k x' x) = (term260 A K k x' x).
Proof. exact (MK_COMB (@lem4433635 A K k x' x) (@lem4433705 A K k x' x)). Qed.
Lemma lem4433708 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4433709 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term218 K P Q) = (term219 K P Q).
Proof. exact (@lem4433708 K P Q). Qed.
Lemma lem4433710 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term261 A K k x' x) = (term262 A K k x' x).
Proof. exact (@lem4433709 K (term215 A K k x' x) (term258 A K k x' x)). Qed.
Lemma lem4433711 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term263 A K k x' x i) = (term213 A K k x' x i).
Proof. exact (eq_refl (term263 A K k x' x i)). Qed.
Lemma lem4433712 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term264 A K k x' x) = (term215 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433711 A K k x' x i)). Qed.
Lemma lem4433713 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433714 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term265 A K k x' x) = (term216 A K k x' x).
Proof. exact (MK_COMB (@lem4433713 K) (@lem4433712 A K k x' x)). Qed.
Lemma lem4433715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433716 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term266 A K k x' x) = (term217 A K k x' x).
Proof. exact (MK_COMB (@lem4433715) (@lem4433714 A K k x' x)). Qed.
Lemma lem4433717 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term267 A K k x' x i) = (term256 A K k i x' x).
Proof. exact (eq_refl (term267 A K k x' x i)). Qed.
Lemma lem4433718 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term268 A K k x' x) = (term258 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433717 A K k i x' x)). Qed.
Lemma lem4433719 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433720 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term269 A K k x' x) = (term259 A K k x' x).
Proof. exact (MK_COMB (@lem4433719 K) (@lem4433718 A K k x' x)). Qed.
Lemma lem4433721 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term261 A K k x' x) = (term260 A K k x' x).
Proof. exact (MK_COMB (@lem4433716 A K k x' x) (@lem4433720 A K k x' x)). Qed.
Lemma lem4433722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433723 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term270 A K k x' x) = (term271 A K k x' x).
Proof. exact (MK_COMB (@lem4433722) (@lem4433721 A K k x' x)). Qed.
Lemma lem4433724 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term263 A K k x' x i) = (term213 A K k x' x i).
Proof. exact (eq_refl (term263 A K k x' x i)). Qed.
Lemma lem4433725 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433726 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term272 A K k x' x i) = (term273 A K k x' x i).
Proof. exact (MK_COMB (@lem4433725) (@lem4433724 A K k x' x i)). Qed.
Lemma lem4433727 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term267 A K k x' x i) = (term256 A K k i x' x).
Proof. exact (eq_refl (term267 A K k x' x i)). Qed.
Lemma lem4433728 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term274 A K k x' x i) = (term275 A K k i x' x).
Proof. exact (MK_COMB (@lem4433726 A K k x' x i) (@lem4433727 A K k i x' x)). Qed.
Lemma lem4433729 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term276 A K k x' x) = (term277 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433728 A K k i x' x)). Qed.
Lemma lem4433730 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4433731 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term262 A K k x' x) = (term278 A K k x' x).
Proof. exact (MK_COMB (@lem4433730 K) (@lem4433729 A K k x' x)). Qed.
Lemma lem4433732 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term261 A K k x' x) = (term262 A K k x' x)) = ((term260 A K k x' x) = (term278 A K k x' x)).
Proof. exact (MK_COMB (@lem4433723 A K k x' x) (@lem4433731 A K k x' x)). Qed.
Lemma lem4433733 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term260 A K k x' x) = (term278 A K k x' x).
Proof. exact (EQ_MP (@lem4433732 A K k x' x) (@lem4433710 A K k x' x)). Qed.
Lemma lem4433736 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term279 A K k x' x) = (term279 A K k x' x).
Proof. exact (eq_refl (term279 A K k x' x)). Qed.
Lemma lem4433737 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term279 A K k x' x) = ((term260 A K k x' x) = (term278 A K k x' x)).
Proof. exact (eq_refl (term279 A K k x' x)). Qed.
Lemma lem4433738 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term280 A K k x' x) = (term280 A K k x' x).
Proof. exact (eq_refl (term280 A K k x' x)). Qed.
Lemma lem4433739 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term279 A K k x' x) = (term279 A K k x' x)) = ((term279 A K k x' x) = ((term260 A K k x' x) = (term278 A K k x' x))).
Proof. exact (MK_COMB (@lem4433738 A K k x' x) (@lem4433737 A K k x' x)). Qed.
Lemma lem4433740 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term279 A K k x' x) = ((term260 A K k x' x) = (term278 A K k x' x)).
Proof. exact (eq_refl (term279 A K k x' x)). Qed.
Lemma lem4433741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4433742 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term280 A K k x' x) = (term281 A K k x' x).
Proof. exact (MK_COMB (@lem4433741) (@lem4433740 A K k x' x)). Qed.
Lemma lem4433743 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term260 A K k x' x) = (term278 A K k x' x)) = ((term260 A K k x' x) = (term278 A K k x' x)).
Proof. exact (eq_refl ((term260 A K k x' x) = (term278 A K k x' x))). Qed.
Lemma lem4433744 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term279 A K k x' x) = ((term260 A K k x' x) = (term278 A K k x' x))) = (((term260 A K k x' x) = (term278 A K k x' x)) = ((term260 A K k x' x) = (term278 A K k x' x))).
Proof. exact (MK_COMB (@lem4433742 A K k x' x) (@lem4433743 A K k x' x)). Qed.
Lemma lem4433745 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term279 A K k x' x) = (term279 A K k x' x)) = (((term260 A K k x' x) = (term278 A K k x' x)) = ((term260 A K k x' x) = (term278 A K k x' x))).
Proof. exact (TRANS (@lem4433739 A K k x' x) (@lem4433744 A K k x' x)). Qed.
Lemma lem4433746 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : ((term260 A K k x' x) = (term278 A K k x' x)) = ((term260 A K k x' x) = (term278 A K k x' x)).
Proof. exact (EQ_MP (@lem4433745 A K k x' x) (@lem4433736 A K k x' x)). Qed.
Lemma lem4433747 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term260 A K k x' x) = (term278 A K k x' x).
Proof. exact (EQ_MP (@lem4433746 A K k x' x) (@lem4433733 A K k x' x)). Qed.
Lemma lem4433749 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term202 A K k x' x) = (term278 A K k x' x).
Proof. exact (TRANS (@lem4433706 A K k x' x) (@lem4433747 A K k x' x)). Qed.
Lemma lem4433750 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term144 A K k x' x) = (term278 A K k x' x).
Proof. exact (TRANS (@lem4433412 A K k x' x) (@lem4433749 A K k x' x)). Qed.
Lemma lem4433751 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (h1 : term144 A K k x' x) : term278 A K k x' x.
Proof. exact (EQ_MP (@lem4433750 A K k x' x) (@lem4433257 A K k x' x h1)). Qed.
Lemma lem4433752 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term275 A K k i x' x) : term275 A K k i x' x.
Proof. exact (h1). Qed.
Lemma lem4433767 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term149 A K k x x') = (term149 A K k x x').
Proof. exact (eq_refl (term149 A K k x x')). Qed.
Lemma lem4433768 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term151 A K k x) = (term151 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4433767 A K k x x')). Qed.
Lemma lem4433769 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433770 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term152 A K k x) = (term152 A K k x).
Proof. exact (MK_COMB (@lem4433769 K) (@lem4433768 A K k x)). Qed.
Lemma lem4433771 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term152 A K k x.
Proof. exact (EQ_MP (@lem4433770 A K k x) (@lem4433322 A K k x h1)). Qed.
Lemma lem4433780 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : ((x' x'') = (x x'')) = ((x' x'') = (x x'')).
Proof. exact (eq_refl ((x' x'') = (x x''))). Qed.
Lemma lem4433781 {A K : Type'} (x' : K -> A) (x : K -> A) : (term140 A K x' x) = (term140 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433780 A K x' x x'')). Qed.
Lemma lem4433782 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433783 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (MK_COMB (@lem4433782 K) (@lem4433781 A K x' x)). Qed.
Lemma lem4433826 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term254 A K k x' x i) = (term254 A K k x' x i).
Proof. exact (eq_refl (term254 A K k x' x i)). Qed.
Lemma lem4433827 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term256 A K k i x' x) = (term256 A K k i x' x).
Proof. exact (MK_COMB (@lem4433826 A K k x' x i) (@lem4433783 A K x' x)). Qed.
Lemma lem4433838 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term187 A K x' x i) = (term187 A K x' x i).
Proof. exact (eq_refl (term187 A K x' x i)). Qed.
Lemma lem4433857 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term166 A K k x' x i) = (term166 A K k x' x i).
Proof. exact (eq_refl (term166 A K k x' x i)). Qed.
Lemma lem4433858 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term174 A K k x' x) = (term174 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433857 A K k x' x i)). Qed.
Lemma lem4433859 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433860 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term175 A K k x' x) = (term175 A K k x' x).
Proof. exact (MK_COMB (@lem4433859 K) (@lem4433858 A K k x' x)). Qed.
Lemma lem4433875 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term149 A K k x' x) = (term149 A K k x' x).
Proof. exact (eq_refl (term149 A K k x' x)). Qed.
Lemma lem4433876 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term151 A K k x') = (term151 A K k x').
Proof. exact (fun_ext (fun x : K => @lem4433875 A K k x' x)). Qed.
Lemma lem4433877 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433878 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term152 A K k x') = (term152 A K k x').
Proof. exact (MK_COMB (@lem4433877 K) (@lem4433876 A K k x')). Qed.
Lemma lem4433879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433880 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term181 A K k x') = (term181 A K k x').
Proof. exact (MK_COMB (@lem4433879) (@lem4433878 A K k x')). Qed.
Lemma lem4433881 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term182 A K k x' x) = (term182 A K k x' x).
Proof. exact (MK_COMB (@lem4433880 A K k x') (@lem4433860 A K k x' x)). Qed.
Lemma lem4433882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4433883 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term196 A K k x' x) = (term196 A K k x' x).
Proof. exact (MK_COMB (@lem4433882) (@lem4433881 A K k x' x)). Qed.
Lemma lem4433884 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term213 A K k x' x i) = (term213 A K k x' x i).
Proof. exact (MK_COMB (@lem4433883 A K k x' x) (@lem4433838 A K x' x i)). Qed.
Lemma lem4433885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4433886 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term273 A K k x' x i) = (term273 A K k x' x i).
Proof. exact (MK_COMB (@lem4433885) (@lem4433884 A K k x' x i)). Qed.
Lemma lem4433887 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) : (term275 A K k i x' x) = (term275 A K k i x' x).
Proof. exact (MK_COMB (@lem4433886 A K k x' x i) (@lem4433827 A K k i x' x)). Qed.
Lemma lem4433888 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term275 A K k i x' x) : term275 A K k i x' x.
Proof. exact (EQ_MP (@lem4433887 A K k i x' x) (@lem4433752 A K k i x' x h1)). Qed.
Lemma lem4433889 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term213 A K k x' x i.
Proof. exact (h1). Qed.
Lemma lem4433890 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term256 A K k i x' x.
Proof. exact (h1). Qed.
Lemma lem4433892 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term182 A K k x' x.
Proof. exact (proj1 (@lem4433889 A K k x' x i h1)). Qed.
Lemma lem4433893 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term175 A K k x' x.
Proof. exact (proj2 (@lem4433892 A K k x' x i h1)). Qed.
Lemma lem4433894 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term152 A K k x'.
Proof. exact (proj1 (@lem4433892 A K k x' x i h1)). Qed.
Lemma lem4433895 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term124 A K x' x.
Proof. exact (proj2 (@lem4433890 A K k i x' x h1)). Qed.
Lemma lem4433896 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term234 A K k x' x i.
Proof. exact (proj1 (@lem4433890 A K k i x' x h1)). Qed.
Lemma lem4433897 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term154 A K k x' i.
Proof. exact (h1). Qed.
Lemma lem4433898 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term165 A K k x' x i) : term165 A K k x' x i.
Proof. exact (h1). Qed.
Lemma lem4433910 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term149 A K k x x') = (term149 A K k x x').
Proof. exact (eq_refl (term149 A K k x x')). Qed.
Lemma lem4433911 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term151 A K k x) = (term151 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4433910 A K k x x')). Qed.
Lemma lem4433912 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433914 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term152 A K k x) = (term152 A K k x).
Proof. exact (MK_COMB (@lem4433912 K) (@lem4433911 A K k x)). Qed.
Lemma lem4433915 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term152 A K k x.
Proof. exact (EQ_MP (@lem4433914 A K k x) (@lem4433771 A K k x h1)). Qed.
Lemma lem4433927 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K) : (term149 A K k x' x) = (term149 A K k x' x).
Proof. exact (eq_refl (term149 A K k x' x)). Qed.
Lemma lem4433928 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term151 A K k x') = (term151 A K k x').
Proof. exact (fun_ext (fun x : K => @lem4433927 A K k x' x)). Qed.
Lemma lem4433929 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433931 {A K : Type'} (k : K -> Prop) (x' : K -> A) : (term152 A K k x') = (term152 A K k x').
Proof. exact (MK_COMB (@lem4433929 K) (@lem4433928 A K k x')). Qed.
Lemma lem4433932 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term152 A K k x'.
Proof. exact (EQ_MP (@lem4433931 A K k x') (@lem4433894 A K k x' x i h1)). Qed.
Lemma lem4433940 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) : (term166 A K k x' x i) = (term166 A K k x' x i).
Proof. exact (eq_refl (term166 A K k x' x i)). Qed.
Lemma lem4433941 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term174 A K k x' x) = (term174 A K k x' x).
Proof. exact (fun_ext (fun i : K => @lem4433940 A K k x' x i)). Qed.
Lemma lem4433942 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433944 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) : (term175 A K k x' x) = (term175 A K k x' x).
Proof. exact (MK_COMB (@lem4433942 K) (@lem4433941 A K k x' x)). Qed.
Lemma lem4433945 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term175 A K k x' x.
Proof. exact (EQ_MP (@lem4433944 A K k x' x) (@lem4433893 A K k x' x i h1)). Qed.
Lemma lem4433953 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term149 A K k x x') = (term149 A K k x x').
Proof. exact (eq_refl (term149 A K k x x')). Qed.
Lemma lem4433954 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term151 A K k x) = (term151 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4433953 A K k x x')). Qed.
Lemma lem4433955 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433957 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term152 A K k x) = (term152 A K k x).
Proof. exact (MK_COMB (@lem4433955 K) (@lem4433954 A K k x)). Qed.
Lemma lem4433958 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term152 A K k x.
Proof. exact (EQ_MP (@lem4433957 A K k x) (@lem4433771 A K k x h1)). Qed.
Lemma lem4433960 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : ((x' x'') = (x x'')) = ((x' x'') = (x x'')).
Proof. exact (eq_refl ((x' x'') = (x x''))). Qed.
Lemma lem4433961 {A K : Type'} (x' : K -> A) (x : K -> A) : (term140 A K x' x) = (term140 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433960 A K x' x x'')). Qed.
Lemma lem4433962 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433964 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (MK_COMB (@lem4433962 K) (@lem4433961 A K x' x)). Qed.
Lemma lem4433965 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term124 A K x' x.
Proof. exact (EQ_MP (@lem4433964 A K x' x) (@lem4433895 A K k i x' x h1)). Qed.
Lemma lem4433988 {A K : Type'} (x' : K -> A) (x : K -> A) (x'' : K) : ((x' x'') = (x x'')) = ((x' x'') = (x x'')).
Proof. exact (eq_refl ((x' x'') = (x x''))). Qed.
Lemma lem4433989 {A K : Type'} (x' : K -> A) (x : K -> A) : (term140 A K x' x) = (term140 A K x' x).
Proof. exact (fun_ext (fun x'' : K => @lem4433988 A K x' x x'')). Qed.
Lemma lem4433990 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4433992 {A K : Type'} (x' : K -> A) (x : K -> A) : (term124 A K x' x) = (term124 A K x' x).
Proof. exact (MK_COMB (@lem4433990 K) (@lem4433989 A K x' x)). Qed.
Lemma lem4433993 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term124 A K x' x.
Proof. exact (EQ_MP (@lem4433992 A K x' x) (@lem4433895 A K k i x' x h1)). Qed.
Lemma lem4434002 {A K : Type'} (_50995 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term282 A K k x _50995.
Proof. exact (@lem4433915 A K k x h1 _50995). Qed.
Lemma lem4434003 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50995 : K) : (term282 A K k x _50995) = (term149 A K k x _50995).
Proof. exact (eq_refl (term282 A K k x _50995)). Qed.
Lemma lem4434005 {A K : Type'} (_50996 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term282 A K k x' _50996.
Proof. exact (@lem4433932 A K k x' x i h1 _50996). Qed.
Lemma lem4434006 {A K : Type'} (k : K -> Prop) (x' : K -> A) (_50996 : K) : (term282 A K k x' _50996) = (term149 A K k x' _50996).
Proof. exact (eq_refl (term282 A K k x' _50996)). Qed.
Lemma lem4434008 {A K : Type'} (_50997 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term283 A K k x' x _50997.
Proof. exact (@lem4433945 A K k x' x i h1 _50997). Qed.
Lemma lem4434009 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (_50997 : K) : (term283 A K k x' x _50997) = (term166 A K k x' x _50997).
Proof. exact (eq_refl (term283 A K k x' x _50997)). Qed.
Lemma lem4434011 {A K : Type'} (_50998 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term282 A K k x _50998.
Proof. exact (@lem4433958 A K k x h1 _50998). Qed.
Lemma lem4434012 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50998 : K) : (term282 A K k x _50998) = (term149 A K k x _50998).
Proof. exact (eq_refl (term282 A K k x _50998)). Qed.
Lemma lem4434014 {A K : Type'} (_50999 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term185 A K x' x _50999.
Proof. exact (@lem4433965 A K k i x' x h1 _50999). Qed.
Lemma lem4434015 {A K : Type'} (x' : K -> A) (x : K -> A) (_50999 : K) : (term185 A K x' x _50999) = ((x' _50999) = (x _50999)).
Proof. exact (eq_refl (term185 A K x' x _50999)). Qed.
Lemma lem4434020 {A K : Type'} (_51001 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term185 A K x' x _51001.
Proof. exact (@lem4433993 A K k i x' x h1 _51001). Qed.
Lemma lem4434021 {A K : Type'} (x' : K -> A) (x : K -> A) (_51001 : K) : (term185 A K x' x _51001) = ((x' _51001) = (x _51001)).
Proof. exact (eq_refl (term185 A K x' x _51001)). Qed.
Lemma lem4434028 {A K : Type'} (_50995 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term149 A K k x _50995.
Proof. exact (EQ_MP (@lem4434003 A K k x _50995) (@lem4434002 A K _50995 k x h1)). Qed.
Lemma lem4434030 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term187 A K x' x i.
Proof. exact (proj2 (@lem4433889 A K k x' x i h1)). Qed.
Lemma lem4434036 {A K : Type'} (_50996 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term149 A K k x' _50996.
Proof. exact (EQ_MP (@lem4434006 A K k x' _50996) (@lem4434005 A K _50996 k x' x i h1)). Qed.
Lemma lem4434042 {A K : Type'} (_50997 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term166 A K k x' x _50997.
Proof. exact (EQ_MP (@lem4434009 A K k x' x _50997) (@lem4434008 A K _50997 k x' x i h1)). Qed.
Lemma lem4434048 {A K : Type'} (_50998 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term149 A K k x _50998.
Proof. exact (EQ_MP (@lem4434012 A K k x _50998) (@lem4434011 A K _50998 k x h1)). Qed.
Lemma lem4434054 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term284 A K x' i.
Proof. exact (proj2 (@lem4433897 A K k x' i h1)). Qed.
Lemma lem4434066 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term165 A K k x' x i) : term187 A K x' x i.
Proof. exact (proj2 (@lem4433898 A K k x' x i h1)). Qed.
Lemma lem4434103 {A : Type'} (x : A) (y : A) (z : A) : term285 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4434109 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4434110 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4434109 A x). Qed.
Lemma lem4434111 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (x' i).
Proof. exact (@lem4434110 A (x' i)). Qed.
Lemma lem4434112 {A K : Type'} (x' : K -> A) (i : K) : term286 A K x' i.
Proof. exact (fun h0 : term287 A K x' i => @lem4434111 A K x' i). Qed.
Lemma lem4434114 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434115 {A K : Type'} (x' : K -> A) (i : K) : (term286 A K x' i) = ((x' i) = (x' i)).
Proof. exact (@lem4434114 ((x' i) = (x' i))). Qed.
Lemma lem4434116 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (x' i).
Proof. exact (EQ_MP (@lem4434115 A K x' i) (@lem4434112 A K x' i)). Qed.
Lemma lem4434119 {K : Type'} (i : K) (k : K -> Prop) (h1 : term150 K i k) : term150 K i k.
Proof. exact (h1). Qed.
Lemma lem4434120 {K : Type'} (i : K) (k : K -> Prop) (h1 : term150 K i k) : term289 K i k.
Proof. exact (fun h0 : @IN K i k => @lem4434119 K i k h1). Qed.
Lemma lem4434122 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4434123 {K : Type'} (i : K) (k : K -> Prop) : (term289 K i k) = (term150 K i k).
Proof. exact (@lem4434122 (@IN K i k)). Qed.
Lemma lem4434124 {K : Type'} (i : K) (k : K -> Prop) (h1 : term150 K i k) : term150 K i k.
Proof. exact (EQ_MP (@lem4434123 K i k) (@lem4434120 K i k h1)). Qed.
Lemma lem4434130 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4434131 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : (term149 A K k x _50995) = (term291 A K x _50995 k).
Proof. exact (@lem4434130 ((x _50995) = (@ARB A)) (@IN K _50995 k)). Qed.
Lemma lem4434139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4434140 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : (term292 A K k x _50995) = (term293 A K x _50995 k).
Proof. exact (MK_COMB (@lem4434139) (@lem4434131 A K x _50995 k)). Qed.
Lemma lem4434148 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : (term291 A K x _50995 k) = (term291 A K x _50995 k).
Proof. exact (eq_refl (term291 A K x _50995 k)). Qed.
Lemma lem4434149 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : ((term149 A K k x _50995) = (term291 A K x _50995 k)) = ((term291 A K x _50995 k) = (term291 A K x _50995 k)).
Proof. exact (MK_COMB (@lem4434140 A K x _50995 k) (@lem4434148 A K x _50995 k)). Qed.
Lemma lem4434151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4434152 (x : Prop) : (x = x) = True.
Proof. exact (@lem4434151 Prop x). Qed.
Lemma lem4434153 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : ((term291 A K x _50995 k) = (term291 A K x _50995 k)) = True.
Proof. exact (@lem4434152 (term291 A K x _50995 k)). Qed.
Lemma lem4434154 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : ((term149 A K k x _50995) = (term291 A K x _50995 k)) = True.
Proof. exact (TRANS (@lem4434149 A K x _50995 k) (@lem4434153 A K x _50995 k)). Qed.
Lemma lem4434155 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : True = ((term149 A K k x _50995) = (term291 A K x _50995 k)).
Proof. exact (SYM (@lem4434154 A K x _50995 k)). Qed.
Lemma lem4434156 {A K : Type'} (x : K -> A) (_50995 : K) (k : K -> Prop) : (term149 A K k x _50995) = (term291 A K x _50995 k).
Proof. exact (EQ_MP (@lem4434155 A K x _50995 k) (@lem0)). Qed.
Lemma lem4434157 {A K : Type'} (_50995 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term291 A K x _50995 k.
Proof. exact (EQ_MP (@lem4434156 A K x _50995 k) (@lem4434028 A K _50995 k x h1)). Qed.
Lemma lem4434159 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434162 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50995 : K) : (term291 A K x _50995 k) = (term141 A K k x _50995).
Proof. exact (@lem4434159 (@IN K _50995 k) ((x _50995) = (@ARB A))). Qed.
Lemma lem4434165 {A K : Type'} (_50995 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x _50995.
Proof. exact (EQ_MP (@lem4434162 A K k x _50995) (@lem4434157 A K _50995 k x h1)). Qed.
Lemma lem4434166 {A K : Type'} (_50995 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x _50995.
Proof. exact (@lem4434165 A K _50995 k x h1). Qed.
Lemma lem4434167 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x i.
Proof. exact (@lem4434166 A K i k x h1). Qed.
Lemma lem4434170 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : (x i) = (@ARB A).
Proof. exact (@lem4434167 A K i k x h1 (@lem4434124 K i k h2)). Qed.
Lemma lem4434171 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : term295 A K x i.
Proof. exact (fun h0 : term284 A K x i => @lem4434170 A K x i k h1 h2). Qed.
Lemma lem4434173 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434174 {A K : Type'} (x : K -> A) (i : K) : (term295 A K x i) = ((x i) = (@ARB A)).
Proof. exact (@lem4434173 ((x i) = (@ARB A))). Qed.
Lemma lem4434175 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : (x i) = (@ARB A).
Proof. exact (EQ_MP (@lem4434174 A K x i) (@lem4434171 A K x i k h1 h2)). Qed.
Lemma lem4434177 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4434178 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4434177 A x). Qed.
Lemma lem4434179 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (@lem4434178 A (x i)). Qed.
Lemma lem4434180 {A K : Type'} (x : K -> A) (i : K) : term286 A K x i.
Proof. exact (fun h0 : term287 A K x i => @lem4434179 A K x i). Qed.
Lemma lem4434182 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434183 {A K : Type'} (x : K -> A) (i : K) : (term286 A K x i) = ((x i) = (x i)).
Proof. exact (@lem4434182 ((x i) = (x i))). Qed.
Lemma lem4434184 {A K : Type'} (x : K -> A) (i : K) : (x i) = (x i).
Proof. exact (EQ_MP (@lem4434183 A K x i) (@lem4434180 A K x i)). Qed.
Lemma lem4434202 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4434203 {A : Type'} (y : A) (x : A) (z : A) : (term296 A x y z) = (term297 A y x z).
Proof. exact (@lem4434202 (y = z) (term298 A x z)). Qed.
Lemma lem4434213 {A : Type'} (x : A) (y : A) : (term299 A x y) = (term299 A x y).
Proof. exact (eq_refl (term299 A x y)). Qed.
Lemma lem4434214 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term300 A y x z).
Proof. exact (MK_COMB (@lem4434213 A x y) (@lem4434203 A y x z)). Qed.
Lemma lem4434218 (q : Prop) (p : Prop) (r : Prop) : (term301 p q r) = (term301 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4434219 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term302 A y x z).
Proof. exact (@lem4434218 (y = z) (term298 A x y) (term298 A x z)). Qed.
Lemma lem4434241 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term302 A y x z).
Proof. exact (TRANS (@lem4434214 A y x z) (@lem4434219 A y x z)). Qed.
Lemma lem4434242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4434243 {A : Type'} (y : A) (x : A) (z : A) : (term303 A x y z) = (term304 A y x z).
Proof. exact (MK_COMB (@lem4434242) (@lem4434241 A y x z)). Qed.
Lemma lem4434265 {A : Type'} (y : A) (x : A) (z : A) : (term302 A y x z) = (term302 A y x z).
Proof. exact (eq_refl (term302 A y x z)). Qed.
Lemma lem4434266 {A : Type'} (y : A) (x : A) (z : A) : ((term285 A x y z) = (term302 A y x z)) = ((term302 A y x z) = (term302 A y x z)).
Proof. exact (MK_COMB (@lem4434243 A y x z) (@lem4434265 A y x z)). Qed.
Lemma lem4434268 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4434269 (x : Prop) : (x = x) = True.
Proof. exact (@lem4434268 Prop x). Qed.
Lemma lem4434270 {A : Type'} (y : A) (x : A) (z : A) : ((term302 A y x z) = (term302 A y x z)) = True.
Proof. exact (@lem4434269 (term302 A y x z)). Qed.
Lemma lem4434271 {A : Type'} (y : A) (x : A) (z : A) : ((term285 A x y z) = (term302 A y x z)) = True.
Proof. exact (TRANS (@lem4434266 A y x z) (@lem4434270 A y x z)). Qed.
Lemma lem4434272 {A : Type'} (y : A) (x : A) (z : A) : True = ((term285 A x y z) = (term302 A y x z)).
Proof. exact (SYM (@lem4434271 A y x z)). Qed.
Lemma lem4434273 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term302 A y x z).
Proof. exact (EQ_MP (@lem4434272 A y x z) (@lem0)). Qed.
Lemma lem4434274 {A : Type'} (y : A) (x : A) (z : A) : term302 A y x z.
Proof. exact (EQ_MP (@lem4434273 A y x z) (@lem4434103 A x y z)). Qed.
Lemma lem4434276 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434277 {A : Type'} (x : A) (y : A) (z : A) : (term302 A y x z) = (term305 A x y z).
Proof. exact (@lem4434276 (term306 A y x z) (y = z)). Qed.
Lemma lem4434279 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4434280 {A : Type'} (y : A) (x : A) (z : A) : (term309 A y x z) = (term310 A y x z).
Proof. exact (@lem4434279 (term298 A x y) (term298 A x z)). Qed.
Lemma lem4434282 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434283 {A : Type'} (x : A) (y : A) : (term311 A x y) = (x = y).
Proof. exact (@lem4434282 (x = y)). Qed.
Lemma lem4434284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4434285 {A : Type'} (x : A) (y : A) : (term312 A x y) = (term313 A x y).
Proof. exact (MK_COMB (@lem4434284) (@lem4434283 A x y)). Qed.
Lemma lem4434287 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434288 {A : Type'} (x : A) (z : A) : (term311 A x z) = (x = z).
Proof. exact (@lem4434287 (x = z)). Qed.
Lemma lem4434289 {A : Type'} (y : A) (x : A) (z : A) : (term310 A y x z) = (term314 A y x z).
Proof. exact (MK_COMB (@lem4434285 A x y) (@lem4434288 A x z)). Qed.
Lemma lem4434290 {A : Type'} (y : A) (x : A) (z : A) : (term309 A y x z) = (term314 A y x z).
Proof. exact (TRANS (@lem4434280 A y x z) (@lem4434289 A y x z)). Qed.
Lemma lem4434291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4434292 {A : Type'} (y : A) (x : A) (z : A) : (term315 A y x z) = (term316 A y x z).
Proof. exact (MK_COMB (@lem4434291) (@lem4434290 A y x z)). Qed.
Lemma lem4434293 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4434294 {A : Type'} (x : A) (y : A) (z : A) : (term305 A x y z) = (term317 A x y z).
Proof. exact (MK_COMB (@lem4434292 A y x z) (@lem4434293 A y z)). Qed.
Lemma lem4434295 {A : Type'} (x : A) (y : A) (z : A) : (term302 A y x z) = (term317 A x y z).
Proof. exact (TRANS (@lem4434277 A x y z) (@lem4434294 A x y z)). Qed.
Lemma lem4434297 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : term318 A K x i.
Proof. exact (conj (@lem4434175 A K x i k h1 h2) (@lem4434184 A K x i)). Qed.
Lemma lem4434299 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (EQ_MP (@lem4434295 A x y z) (@lem4434274 A y x z)). Qed.
Lemma lem4434300 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (@lem4434299 A x y z). Qed.
Lemma lem4434301 {A K : Type'} (x : K -> A) (i : K) : term319 A K x i.
Proof. exact (@lem4434300 A (x i) (@ARB A) (x i)). Qed.
Lemma lem4434304 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : (@ARB A) = (x i).
Proof. exact (@lem4434301 A K x i (@lem4434297 A K x i k h1 h2)). Qed.
Lemma lem4434305 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : term320 A K x i.
Proof. exact (fun h0 : term321 A K x i => @lem4434304 A K x i k h1 h2). Qed.
Lemma lem4434307 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434308 {A K : Type'} (x : K -> A) (i : K) : (term320 A K x i) = ((@ARB A) = (x i)).
Proof. exact (@lem4434307 ((@ARB A) = (x i))). Qed.
Lemma lem4434309 {A K : Type'} (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term150 K i k) : (@ARB A) = (x i).
Proof. exact (EQ_MP (@lem4434308 A K x i) (@lem4434305 A K x i k h1 h2)). Qed.
Lemma lem4434312 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (h1 : term187 A K x' x i) : term187 A K x' x i.
Proof. exact (h1). Qed.
Lemma lem4434313 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (h1 : term187 A K x' x i) : term322 A K x' x i.
Proof. exact (fun h0 : (x' i) = (x i) => @lem4434312 A K x' x i h1). Qed.
Lemma lem4434315 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4434316 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term322 A K x' x i) = (term187 A K x' x i).
Proof. exact (@lem4434315 ((x' i) = (x i))). Qed.
Lemma lem4434317 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (h1 : term187 A K x' x i) : term187 A K x' x i.
Proof. exact (EQ_MP (@lem4434316 A K x' x i) (@lem4434313 A K x' x i h1)). Qed.
Lemma lem4434319 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434320 {A : Type'} (z : A) (x : A) (y : A) : (term285 A x y z) = (term323 A z x y).
Proof. exact (@lem4434319 (term296 A x y z) (term298 A x y)). Qed.
Lemma lem4434322 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4434323 {A : Type'} (x : A) (y : A) (z : A) : (term324 A x y z) = (term325 A x y z).
Proof. exact (@lem4434322 (term298 A x z) (y = z)). Qed.
Lemma lem4434325 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434326 {A : Type'} (x : A) (z : A) : (term311 A x z) = (x = z).
Proof. exact (@lem4434325 (x = z)). Qed.
Lemma lem4434327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4434328 {A : Type'} (x : A) (z : A) : (term312 A x z) = (term313 A x z).
Proof. exact (MK_COMB (@lem4434327) (@lem4434326 A x z)). Qed.
Lemma lem4434329 {A : Type'} (y : A) (z : A) : (term298 A y z) = (term298 A y z).
Proof. exact (eq_refl (term298 A y z)). Qed.
Lemma lem4434330 {A : Type'} (x : A) (y : A) (z : A) : (term325 A x y z) = (term326 A x y z).
Proof. exact (MK_COMB (@lem4434328 A x z) (@lem4434329 A y z)). Qed.
Lemma lem4434331 {A : Type'} (x : A) (y : A) (z : A) : (term324 A x y z) = (term326 A x y z).
Proof. exact (TRANS (@lem4434323 A x y z) (@lem4434330 A x y z)). Qed.
Lemma lem4434332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4434333 {A : Type'} (x : A) (y : A) (z : A) : (term327 A x y z) = (term328 A x y z).
Proof. exact (MK_COMB (@lem4434332) (@lem4434331 A x y z)). Qed.
Lemma lem4434334 {A : Type'} (x : A) (y : A) : (term298 A x y) = (term298 A x y).
Proof. exact (eq_refl (term298 A x y)). Qed.
Lemma lem4434335 {A : Type'} (z : A) (x : A) (y : A) : (term323 A z x y) = (term329 A z x y).
Proof. exact (MK_COMB (@lem4434333 A x y z) (@lem4434334 A x y)). Qed.
Lemma lem4434336 {A : Type'} (z : A) (x : A) (y : A) : (term285 A x y z) = (term329 A z x y).
Proof. exact (TRANS (@lem4434320 A z x y) (@lem4434335 A z x y)). Qed.
Lemma lem4434338 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term330 A K x' x i.
Proof. exact (conj (@lem4434309 A K x i k h1 h3) (@lem4434317 A K x' x i h2)). Qed.
Lemma lem4434340 {A : Type'} (z : A) (x : A) (y : A) : term329 A z x y.
Proof. exact (EQ_MP (@lem4434336 A z x y) (@lem4434103 A x y z)). Qed.
Lemma lem4434341 {A : Type'} (z : A) (x : A) (y : A) : term329 A z x y.
Proof. exact (@lem4434340 A z x y). Qed.
Lemma lem4434342 {A K : Type'} (x : K -> A) (x' : K -> A) (i : K) : term331 A K x x' i.
Proof. exact (@lem4434341 A (x i) (@ARB A) (x' i)). Qed.
Lemma lem4434345 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term321 A K x' i.
Proof. exact (@lem4434342 A K x x' i (@lem4434338 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434346 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term332 A K x' i.
Proof. exact (fun h0 : (@ARB A) = (x' i) => @lem4434345 A K x' x i k h1 h2 h3). Qed.
Lemma lem4434348 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4434349 {A K : Type'} (x' : K -> A) (i : K) : (term332 A K x' i) = (term321 A K x' i).
Proof. exact (@lem4434348 ((@ARB A) = (x' i))). Qed.
Lemma lem4434350 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term321 A K x' i.
Proof. exact (EQ_MP (@lem4434349 A K x' i) (@lem4434346 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434351 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term333 A K x' i.
Proof. exact (conj (@lem4434116 A K x' i) (@lem4434350 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434353 {A : Type'} (z : A) (x : A) (y : A) : term329 A z x y.
Proof. exact (EQ_MP (@lem4434336 A z x y) (@lem4434103 A x y z)). Qed.
Lemma lem4434354 {A : Type'} (z : A) (x : A) (y : A) : term329 A z x y.
Proof. exact (@lem4434353 A z x y). Qed.
Lemma lem4434355 {A K : Type'} (x' : K -> A) (i : K) : term334 A K x' i.
Proof. exact (@lem4434354 A (x' i) (x' i) (@ARB A)). Qed.
Lemma lem4434358 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term284 A K x' i.
Proof. exact (@lem4434355 A K x' i (@lem4434351 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434359 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term335 A K x' i.
Proof. exact (fun h0 : (x' i) = (@ARB A) => @lem4434358 A K x' x i k h1 h2 h3). Qed.
Lemma lem4434361 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4434362 {A K : Type'} (x' : K -> A) (i : K) : (term335 A K x' i) = (term284 A K x' i).
Proof. exact (@lem4434361 ((x' i) = (@ARB A))). Qed.
Lemma lem4434363 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) (k : K -> Prop) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) : term284 A K x' i.
Proof. exact (EQ_MP (@lem4434362 A K x' i) (@lem4434359 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434365 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434368 {A K : Type'} (x' : K -> A) (_50996 : K) (k : K -> Prop) : (term149 A K k x' _50996) = (term336 A K x' _50996 k).
Proof. exact (@lem4434365 ((x' _50996) = (@ARB A)) (@IN K _50996 k)). Qed.
Lemma lem4434371 {A K : Type'} (_50996 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term336 A K x' _50996 k.
Proof. exact (EQ_MP (@lem4434368 A K x' _50996 k) (@lem4434036 A K _50996 k x' x i h1)). Qed.
Lemma lem4434372 {A K : Type'} (_50996 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term336 A K x' _50996 k.
Proof. exact (@lem4434371 A K _50996 k x' x i h1). Qed.
Lemma lem4434373 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term336 A K x' i k.
Proof. exact (@lem4434372 A K i k x' x i h1). Qed.
Lemma lem4434376 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term150 K i k) (h4 : term213 A K k x' x i) : @IN K i k.
Proof. exact (@lem4434373 A K k x' x i h4 (@lem4434363 A K x' x i k h1 h2 h3)). Qed.
Lemma lem4434377 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term213 A K k x' x i) : term337 K i k.
Proof. exact (fun h0 : term150 K i k => @lem4434376 A K k x' x i h1 h2 h0 h3). Qed.
Lemma lem4434379 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434380 {K : Type'} (i : K) (k : K -> Prop) : (term337 K i k) = (@IN K i k).
Proof. exact (@lem4434379 (@IN K i k)). Qed.
Lemma lem4434381 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term213 A K k x' x i) : @IN K i k.
Proof. exact (EQ_MP (@lem4434380 K i k) (@lem4434377 A K k x' x i h1 h2 h3)). Qed.
Lemma lem4434387 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4434388 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : (term166 A K k x' x _50997) = (term338 A K x' x _50997 k).
Proof. exact (@lem4434387 ((x' _50997) = (x _50997)) (term150 K _50997 k)). Qed.
Lemma lem4434396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4434397 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : (term339 A K k x' x _50997) = (term340 A K x' x _50997 k).
Proof. exact (MK_COMB (@lem4434396) (@lem4434388 A K x' x _50997 k)). Qed.
Lemma lem4434405 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : (term338 A K x' x _50997 k) = (term338 A K x' x _50997 k).
Proof. exact (eq_refl (term338 A K x' x _50997 k)). Qed.
Lemma lem4434406 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : ((term166 A K k x' x _50997) = (term338 A K x' x _50997 k)) = ((term338 A K x' x _50997 k) = (term338 A K x' x _50997 k)).
Proof. exact (MK_COMB (@lem4434397 A K x' x _50997 k) (@lem4434405 A K x' x _50997 k)). Qed.
Lemma lem4434408 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4434409 (x : Prop) : (x = x) = True.
Proof. exact (@lem4434408 Prop x). Qed.
Lemma lem4434410 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : ((term338 A K x' x _50997 k) = (term338 A K x' x _50997 k)) = True.
Proof. exact (@lem4434409 (term338 A K x' x _50997 k)). Qed.
Lemma lem4434411 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : ((term166 A K k x' x _50997) = (term338 A K x' x _50997 k)) = True.
Proof. exact (TRANS (@lem4434406 A K x' x _50997 k) (@lem4434410 A K x' x _50997 k)). Qed.
Lemma lem4434412 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : True = ((term166 A K k x' x _50997) = (term338 A K x' x _50997 k)).
Proof. exact (SYM (@lem4434411 A K x' x _50997 k)). Qed.
Lemma lem4434413 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) (k : K -> Prop) : (term166 A K k x' x _50997) = (term338 A K x' x _50997 k).
Proof. exact (EQ_MP (@lem4434412 A K x' x _50997 k) (@lem0)). Qed.
Lemma lem4434414 {A K : Type'} (_50997 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term338 A K x' x _50997 k.
Proof. exact (EQ_MP (@lem4434413 A K x' x _50997 k) (@lem4434042 A K _50997 k x' x i h1)). Qed.
Lemma lem4434416 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434417 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (_50997 : K) : (term338 A K x' x _50997 k) = (term341 A K k x' x _50997).
Proof. exact (@lem4434416 (term150 K _50997 k) ((x' _50997) = (x _50997))). Qed.
Lemma lem4434419 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434420 {K : Type'} (_50997 : K) (k : K -> Prop) : (term145 K _50997 k) = (@IN K _50997 k).
Proof. exact (@lem4434419 (@IN K _50997 k)). Qed.
Lemma lem4434421 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4434422 {K : Type'} (_50997 : K) (k : K -> Prop) : (term342 K _50997 k) = (term42 K _50997 k).
Proof. exact (MK_COMB (@lem4434421) (@lem4434420 K _50997 k)). Qed.
Lemma lem4434423 {A K : Type'} (x' : K -> A) (x : K -> A) (_50997 : K) : ((x' _50997) = (x _50997)) = ((x' _50997) = (x _50997)).
Proof. exact (eq_refl ((x' _50997) = (x _50997))). Qed.
Lemma lem4434424 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (_50997 : K) : (term341 A K k x' x _50997) = (term44 A K k x' x _50997).
Proof. exact (MK_COMB (@lem4434422 K _50997 k) (@lem4434423 A K x' x _50997)). Qed.
Lemma lem4434425 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (_50997 : K) : (term338 A K x' x _50997 k) = (term44 A K k x' x _50997).
Proof. exact (TRANS (@lem4434417 A K k x' x _50997) (@lem4434424 A K k x' x _50997)). Qed.
Lemma lem4434428 {A K : Type'} (_50997 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term44 A K k x' x _50997.
Proof. exact (EQ_MP (@lem4434425 A K k x' x _50997) (@lem4434414 A K _50997 k x' x i h1)). Qed.
Lemma lem4434429 {A K : Type'} (_50997 : K) (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term44 A K k x' x _50997.
Proof. exact (@lem4434428 A K _50997 k x' x i h1). Qed.
Lemma lem4434430 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term44 A K k x' x i.
Proof. exact (@lem4434429 A K i k x' x i h1). Qed.
Lemma lem4434433 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term187 A K x' x i) (h3 : term213 A K k x' x i) : (x' i) = (x i).
Proof. exact (@lem4434430 A K k x' x i h3 (@lem4434381 A K k x' x i h1 h2 h3)). Qed.
Lemma lem4434434 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term213 A K k x' x i) : term343 A K x' x i.
Proof. exact (fun h0 : term187 A K x' x i => @lem4434433 A K k x' x i h1 h0 h2). Qed.
Lemma lem4434436 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434437 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term343 A K x' x i) = ((x' i) = (x i)).
Proof. exact (@lem4434436 ((x' i) = (x i))). Qed.
Lemma lem4434438 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term213 A K k x' x i) : (x' i) = (x i).
Proof. exact (EQ_MP (@lem4434437 A K x' x i) (@lem4434434 A K k x' x i h1 h2)). Qed.
Lemma lem4434441 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4434443 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term187 A K x' x i) = (term344 A K x' x i).
Proof. exact (@lem4434441 ((x' i) = (x i))). Qed.
Lemma lem4434446 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term213 A K k x' x i) : term344 A K x' x i.
Proof. exact (EQ_MP (@lem4434443 A K x' x i) (@lem4434030 A K k x' x i h1)). Qed.
Lemma lem4434449 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term213 A K k x' x i) : False.
Proof. exact (@lem4434446 A K k x' x i h2 (@lem4434438 A K k x' x i h1 h2)). Qed.
Lemma lem4434450 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term213 A K k x' x i) : term345.
Proof. exact (fun h0 : ~ False => @lem4434449 A K k x' x i h1 h2). Qed.
Lemma lem4434452 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434453 : term345 = False.
Proof. exact (@lem4434452 False). Qed.
Lemma lem4434454 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term213 A K k x' x i) : False.
Proof. exact (EQ_MP (@lem4434453) (@lem4434450 A K k x' x i h1 h2)). Qed.
Lemma lem4434491 {A : Type'} (x : A) (y : A) (z : A) : term285 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem4434497 {A K : Type'} (_50999 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' _50999) = (x _50999).
Proof. exact (EQ_MP (@lem4434015 A K x' x _50999) (@lem4434014 A K _50999 k i x' x h1)). Qed.
Lemma lem4434498 {A K : Type'} (_50999 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' _50999) = (x _50999).
Proof. exact (@lem4434497 A K _50999 k i x' x h1). Qed.
Lemma lem4434499 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' i) = (x i).
Proof. exact (@lem4434498 A K i k i x' x h1). Qed.
Lemma lem4434500 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term343 A K x' x i.
Proof. exact (fun h0 : term187 A K x' x i => @lem4434499 A K k i x' x h1). Qed.
Lemma lem4434502 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434503 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term343 A K x' x i) = ((x' i) = (x i)).
Proof. exact (@lem4434502 ((x' i) = (x i))). Qed.
Lemma lem4434504 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' i) = (x i).
Proof. exact (EQ_MP (@lem4434503 A K x' x i) (@lem4434500 A K k i x' x h1)). Qed.
Lemma lem4434506 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4434507 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4434506 A x). Qed.
Lemma lem4434508 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (x' i).
Proof. exact (@lem4434507 A (x' i)). Qed.
Lemma lem4434509 {A K : Type'} (x' : K -> A) (i : K) : term286 A K x' i.
Proof. exact (fun h0 : term287 A K x' i => @lem4434508 A K x' i). Qed.
Lemma lem4434511 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434512 {A K : Type'} (x' : K -> A) (i : K) : (term286 A K x' i) = ((x' i) = (x' i)).
Proof. exact (@lem4434511 ((x' i) = (x' i))). Qed.
Lemma lem4434513 {A K : Type'} (x' : K -> A) (i : K) : (x' i) = (x' i).
Proof. exact (EQ_MP (@lem4434512 A K x' i) (@lem4434509 A K x' i)). Qed.
Lemma lem4434531 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4434532 {A : Type'} (y : A) (x : A) (z : A) : (term296 A x y z) = (term297 A y x z).
Proof. exact (@lem4434531 (y = z) (term298 A x z)). Qed.
Lemma lem4434542 {A : Type'} (x : A) (y : A) : (term299 A x y) = (term299 A x y).
Proof. exact (eq_refl (term299 A x y)). Qed.
Lemma lem4434543 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term300 A y x z).
Proof. exact (MK_COMB (@lem4434542 A x y) (@lem4434532 A y x z)). Qed.
Lemma lem4434547 (q : Prop) (p : Prop) (r : Prop) : (term301 p q r) = (term301 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4434548 {A : Type'} (y : A) (x : A) (z : A) : (term300 A y x z) = (term302 A y x z).
Proof. exact (@lem4434547 (y = z) (term298 A x y) (term298 A x z)). Qed.
Lemma lem4434570 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term302 A y x z).
Proof. exact (TRANS (@lem4434543 A y x z) (@lem4434548 A y x z)). Qed.
Lemma lem4434571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4434572 {A : Type'} (y : A) (x : A) (z : A) : (term303 A x y z) = (term304 A y x z).
Proof. exact (MK_COMB (@lem4434571) (@lem4434570 A y x z)). Qed.
Lemma lem4434594 {A : Type'} (y : A) (x : A) (z : A) : (term302 A y x z) = (term302 A y x z).
Proof. exact (eq_refl (term302 A y x z)). Qed.
Lemma lem4434595 {A : Type'} (y : A) (x : A) (z : A) : ((term285 A x y z) = (term302 A y x z)) = ((term302 A y x z) = (term302 A y x z)).
Proof. exact (MK_COMB (@lem4434572 A y x z) (@lem4434594 A y x z)). Qed.
Lemma lem4434597 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4434598 (x : Prop) : (x = x) = True.
Proof. exact (@lem4434597 Prop x). Qed.
Lemma lem4434599 {A : Type'} (y : A) (x : A) (z : A) : ((term302 A y x z) = (term302 A y x z)) = True.
Proof. exact (@lem4434598 (term302 A y x z)). Qed.
Lemma lem4434600 {A : Type'} (y : A) (x : A) (z : A) : ((term285 A x y z) = (term302 A y x z)) = True.
Proof. exact (TRANS (@lem4434595 A y x z) (@lem4434599 A y x z)). Qed.
Lemma lem4434601 {A : Type'} (y : A) (x : A) (z : A) : True = ((term285 A x y z) = (term302 A y x z)).
Proof. exact (SYM (@lem4434600 A y x z)). Qed.
Lemma lem4434602 {A : Type'} (y : A) (x : A) (z : A) : (term285 A x y z) = (term302 A y x z).
Proof. exact (EQ_MP (@lem4434601 A y x z) (@lem0)). Qed.
Lemma lem4434603 {A : Type'} (y : A) (x : A) (z : A) : term302 A y x z.
Proof. exact (EQ_MP (@lem4434602 A y x z) (@lem4434491 A x y z)). Qed.
Lemma lem4434605 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434606 {A : Type'} (x : A) (y : A) (z : A) : (term302 A y x z) = (term305 A x y z).
Proof. exact (@lem4434605 (term306 A y x z) (y = z)). Qed.
Lemma lem4434608 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4434609 {A : Type'} (y : A) (x : A) (z : A) : (term309 A y x z) = (term310 A y x z).
Proof. exact (@lem4434608 (term298 A x y) (term298 A x z)). Qed.
Lemma lem4434611 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434612 {A : Type'} (x : A) (y : A) : (term311 A x y) = (x = y).
Proof. exact (@lem4434611 (x = y)). Qed.
Lemma lem4434613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4434614 {A : Type'} (x : A) (y : A) : (term312 A x y) = (term313 A x y).
Proof. exact (MK_COMB (@lem4434613) (@lem4434612 A x y)). Qed.
Lemma lem4434616 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4434617 {A : Type'} (x : A) (z : A) : (term311 A x z) = (x = z).
Proof. exact (@lem4434616 (x = z)). Qed.
Lemma lem4434618 {A : Type'} (y : A) (x : A) (z : A) : (term310 A y x z) = (term314 A y x z).
Proof. exact (MK_COMB (@lem4434614 A x y) (@lem4434617 A x z)). Qed.
Lemma lem4434619 {A : Type'} (y : A) (x : A) (z : A) : (term309 A y x z) = (term314 A y x z).
Proof. exact (TRANS (@lem4434609 A y x z) (@lem4434618 A y x z)). Qed.
Lemma lem4434620 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4434621 {A : Type'} (y : A) (x : A) (z : A) : (term315 A y x z) = (term316 A y x z).
Proof. exact (MK_COMB (@lem4434620) (@lem4434619 A y x z)). Qed.
Lemma lem4434622 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4434623 {A : Type'} (x : A) (y : A) (z : A) : (term305 A x y z) = (term317 A x y z).
Proof. exact (MK_COMB (@lem4434621 A y x z) (@lem4434622 A y z)). Qed.
Lemma lem4434624 {A : Type'} (x : A) (y : A) (z : A) : (term302 A y x z) = (term317 A x y z).
Proof. exact (TRANS (@lem4434606 A x y z) (@lem4434623 A x y z)). Qed.
Lemma lem4434626 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term346 A K x x' i.
Proof. exact (conj (@lem4434504 A K k i x' x h1) (@lem4434513 A K x' i)). Qed.
Lemma lem4434628 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (EQ_MP (@lem4434624 A x y z) (@lem4434603 A y x z)). Qed.
Lemma lem4434629 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (@lem4434628 A x y z). Qed.
Lemma lem4434630 {A K : Type'} (x : K -> A) (x' : K -> A) (i : K) : term347 A K x x' i.
Proof. exact (@lem4434629 A (x' i) (x i) (x' i)). Qed.
Lemma lem4434633 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x i) = (x' i).
Proof. exact (@lem4434630 A K x x' i (@lem4434626 A K k i x' x h1)). Qed.
Lemma lem4434634 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term343 A K x x' i.
Proof. exact (fun h0 : term187 A K x x' i => @lem4434633 A K k i x' x h1). Qed.
Lemma lem4434636 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434637 {A K : Type'} (x : K -> A) (x' : K -> A) (i : K) : (term343 A K x x' i) = ((x i) = (x' i)).
Proof. exact (@lem4434636 ((x i) = (x' i))). Qed.
Lemma lem4434638 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x i) = (x' i).
Proof. exact (EQ_MP (@lem4434637 A K x x' i) (@lem4434634 A K k i x' x h1)). Qed.
Lemma lem4434640 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term150 K i k.
Proof. exact (proj1 (@lem4433897 A K k x' i h1)). Qed.
Lemma lem4434641 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term289 K i k.
Proof. exact (fun h0 : @IN K i k => @lem4434640 A K k x' i h1). Qed.
Lemma lem4434643 (p : Prop) : (term290 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4434644 {K : Type'} (i : K) (k : K -> Prop) : (term289 K i k) = (term150 K i k).
Proof. exact (@lem4434643 (@IN K i k)). Qed.
Lemma lem4434645 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term150 K i k.
Proof. exact (EQ_MP (@lem4434644 K i k) (@lem4434641 A K k x' i h1)). Qed.
Lemma lem4434651 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4434652 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : (term149 A K k x _50998) = (term291 A K x _50998 k).
Proof. exact (@lem4434651 ((x _50998) = (@ARB A)) (@IN K _50998 k)). Qed.
Lemma lem4434660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4434661 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : (term292 A K k x _50998) = (term293 A K x _50998 k).
Proof. exact (MK_COMB (@lem4434660) (@lem4434652 A K x _50998 k)). Qed.
Lemma lem4434669 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : (term291 A K x _50998 k) = (term291 A K x _50998 k).
Proof. exact (eq_refl (term291 A K x _50998 k)). Qed.
Lemma lem4434670 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : ((term149 A K k x _50998) = (term291 A K x _50998 k)) = ((term291 A K x _50998 k) = (term291 A K x _50998 k)).
Proof. exact (MK_COMB (@lem4434661 A K x _50998 k) (@lem4434669 A K x _50998 k)). Qed.
Lemma lem4434672 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4434673 (x : Prop) : (x = x) = True.
Proof. exact (@lem4434672 Prop x). Qed.
Lemma lem4434674 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : ((term291 A K x _50998 k) = (term291 A K x _50998 k)) = True.
Proof. exact (@lem4434673 (term291 A K x _50998 k)). Qed.
Lemma lem4434675 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : ((term149 A K k x _50998) = (term291 A K x _50998 k)) = True.
Proof. exact (TRANS (@lem4434670 A K x _50998 k) (@lem4434674 A K x _50998 k)). Qed.
Lemma lem4434676 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : True = ((term149 A K k x _50998) = (term291 A K x _50998 k)).
Proof. exact (SYM (@lem4434675 A K x _50998 k)). Qed.
Lemma lem4434677 {A K : Type'} (x : K -> A) (_50998 : K) (k : K -> Prop) : (term149 A K k x _50998) = (term291 A K x _50998 k).
Proof. exact (EQ_MP (@lem4434676 A K x _50998 k) (@lem0)). Qed.
Lemma lem4434678 {A K : Type'} (_50998 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term291 A K x _50998 k.
Proof. exact (EQ_MP (@lem4434677 A K x _50998 k) (@lem4434048 A K _50998 k x h1)). Qed.
Lemma lem4434680 (b : Prop) (a : Prop) : (a \/ b) = (term294 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4434683 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50998 : K) : (term291 A K x _50998 k) = (term141 A K k x _50998).
Proof. exact (@lem4434680 (@IN K _50998 k) ((x _50998) = (@ARB A))). Qed.
Lemma lem4434686 {A K : Type'} (_50998 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x _50998.
Proof. exact (EQ_MP (@lem4434683 A K k x _50998) (@lem4434678 A K _50998 k x h1)). Qed.
Lemma lem4434687 {A K : Type'} (_50998 : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x _50998.
Proof. exact (@lem4434686 A K _50998 k x h1). Qed.
Lemma lem4434688 {A K : Type'} (i : K) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term141 A K k x i.
Proof. exact (@lem4434687 A K i k x h1). Qed.
Lemma lem4434691 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term154 A K k x' i) : (x i) = (@ARB A).
Proof. exact (@lem4434688 A K i k x h1 (@lem4434645 A K k x' i h2)). Qed.
Lemma lem4434692 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term154 A K k x' i) : term295 A K x i.
Proof. exact (fun h0 : term284 A K x i => @lem4434691 A K x k x' i h1 h2). Qed.
Lemma lem4434694 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434695 {A K : Type'} (x : K -> A) (i : K) : (term295 A K x i) = ((x i) = (@ARB A)).
Proof. exact (@lem4434694 ((x i) = (@ARB A))). Qed.
Lemma lem4434696 {A K : Type'} (x : K -> A) (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term82 A K k x) (h2 : term154 A K k x' i) : (x i) = (@ARB A).
Proof. exact (EQ_MP (@lem4434695 A K x i) (@lem4434692 A K x k x' i h1 h2)). Qed.
Lemma lem4434697 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : term348 A K x' x i.
Proof. exact (conj (@lem4434638 A K k i x' x h3) (@lem4434696 A K x k x' i h1 h2)). Qed.
Lemma lem4434699 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (EQ_MP (@lem4434624 A x y z) (@lem4434603 A y x z)). Qed.
Lemma lem4434700 {A : Type'} (x : A) (y : A) (z : A) : term317 A x y z.
Proof. exact (@lem4434699 A x y z). Qed.
Lemma lem4434701 {A K : Type'} (x : K -> A) (x' : K -> A) (i : K) : term349 A K x x' i.
Proof. exact (@lem4434700 A (x i) (x' i) (@ARB A)). Qed.
Lemma lem4434704 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : (x' i) = (@ARB A).
Proof. exact (@lem4434701 A K x x' i (@lem4434697 A K k i x' x h1 h2 h3)). Qed.
Lemma lem4434705 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : term295 A K x' i.
Proof. exact (fun h0 : term284 A K x' i => @lem4434704 A K k i x' x h1 h2 h3). Qed.
Lemma lem4434707 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434708 {A K : Type'} (x' : K -> A) (i : K) : (term295 A K x' i) = ((x' i) = (@ARB A)).
Proof. exact (@lem4434707 ((x' i) = (@ARB A))). Qed.
Lemma lem4434709 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : (x' i) = (@ARB A).
Proof. exact (EQ_MP (@lem4434708 A K x' i) (@lem4434705 A K k i x' x h1 h2 h3)). Qed.
Lemma lem4434712 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4434714 {A K : Type'} (x' : K -> A) (i : K) : (term284 A K x' i) = (term350 A K x' i).
Proof. exact (@lem4434712 ((x' i) = (@ARB A))). Qed.
Lemma lem4434717 {A K : Type'} (k : K -> Prop) (x' : K -> A) (i : K) (h1 : term154 A K k x' i) : term350 A K x' i.
Proof. exact (EQ_MP (@lem4434714 A K x' i) (@lem4434054 A K k x' i h1)). Qed.
Lemma lem4434720 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : False.
Proof. exact (@lem4434717 A K k x' i h2 (@lem4434709 A K k i x' x h1 h2 h3)). Qed.
Lemma lem4434721 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : term345.
Proof. exact (fun h0 : ~ False => @lem4434720 A K k i x' x h1 h2 h3). Qed.
Lemma lem4434723 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434724 : term345 = False.
Proof. exact (@lem4434723 False). Qed.
Lemma lem4434725 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term154 A K k x' i) (h3 : term256 A K k i x' x) : False.
Proof. exact (EQ_MP (@lem4434724) (@lem4434721 A K k i x' x h1 h2 h3)). Qed.
Lemma lem4434768 {A K : Type'} (_51001 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' _51001) = (x _51001).
Proof. exact (EQ_MP (@lem4434021 A K x' x _51001) (@lem4434020 A K _51001 k i x' x h1)). Qed.
Lemma lem4434769 {A K : Type'} (_51001 : K) (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' _51001) = (x _51001).
Proof. exact (@lem4434768 A K _51001 k i x' x h1). Qed.
Lemma lem4434770 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' i) = (x i).
Proof. exact (@lem4434769 A K i k i x' x h1). Qed.
Lemma lem4434771 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : term343 A K x' x i.
Proof. exact (fun h0 : term187 A K x' x i => @lem4434770 A K k i x' x h1). Qed.
Lemma lem4434773 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434774 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term343 A K x' x i) = ((x' i) = (x i)).
Proof. exact (@lem4434773 ((x' i) = (x i))). Qed.
Lemma lem4434775 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term256 A K k i x' x) : (x' i) = (x i).
Proof. exact (EQ_MP (@lem4434774 A K x' x i) (@lem4434771 A K k i x' x h1)). Qed.
Lemma lem4434778 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4434780 {A K : Type'} (x' : K -> A) (x : K -> A) (i : K) : (term187 A K x' x i) = (term344 A K x' x i).
Proof. exact (@lem4434778 ((x' i) = (x i))). Qed.
Lemma lem4434783 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (i : K) (h1 : term165 A K k x' x i) : term344 A K x' x i.
Proof. exact (EQ_MP (@lem4434780 A K x' x i) (@lem4434066 A K k x' x i h1)). Qed.
Lemma lem4434786 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term165 A K k x' x i) (h2 : term256 A K k i x' x) : False.
Proof. exact (@lem4434783 A K k x' x i h1 (@lem4434775 A K k i x' x h2)). Qed.
Lemma lem4434787 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term165 A K k x' x i) (h2 : term256 A K k i x' x) : term345.
Proof. exact (fun h0 : ~ False => @lem4434786 A K k i x' x h1 h2). Qed.
Lemma lem4434789 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4434790 : term345 = False.
Proof. exact (@lem4434789 False). Qed.
Lemma lem4434791 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term165 A K k x' x i) (h2 : term256 A K k i x' x) : False.
Proof. exact (EQ_MP (@lem4434790) (@lem4434787 A K k i x' x h1 h2)). Qed.
Lemma lem4434792 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term256 A K k i x' x) : False.
Proof. exact (or_elim (@lem4433896 A K k i x' x h2) (fun h0 : term154 A K k x' i => @lem4434725 A K k i x' x h1 h0 h2) (fun h0 : term165 A K k x' x i => @lem4434791 A K k i x' x h0 h2)). Qed.
Lemma lem4434793 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term275 A K k i x' x) : False.
Proof. exact (or_elim (@lem4433888 A K k i x' x h2) (fun h0 : term213 A K k x' x i => @lem4434454 A K k x' x i h1 h0) (fun h0 : term256 A K k i x' x => @lem4434792 A K k i x' x h1 h0)). Qed.
Lemma lem4434794 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term275 A K k i x' x) : (term275 A K k i x' x) = False.
Proof. exact (prop_ext (fun h3 : term275 A K k i x' x => @lem4434793 A K k i x' x h1 h2) (fun h3 : False => @lem4433888 A K k i x' x h2)). Qed.
Lemma lem4434795 {A K : Type'} (k : K -> Prop) (i : K) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term275 A K k i x' x) : False.
Proof. exact (EQ_MP (@lem4434794 A K k i x' x h1 h2) (@lem4433888 A K k i x' x h2)). Qed.
Lemma lem4434796 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term144 A K k x' x) : False.
Proof. exact (ex_elim (@lem4433751 A K k x' x h2) (fun i : K => fun h0 : term277 A K k x' x i => @lem4434795 A K k i x' x h1 h0)). Qed.
Lemma lem4434797 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term144 A K k x' x) : (term144 A K k x' x) = False.
Proof. exact (prop_ext (fun h3 : term144 A K k x' x => @lem4434796 A K k x' x h1 h2) (fun h3 : False => @lem4433257 A K k x' x h2)). Qed.
Lemma lem4434798 {A K : Type'} (k : K -> Prop) (x' : K -> A) (x : K -> A) (h1 : term82 A K k x) (h2 : term144 A K k x' x) : False.
Proof. exact (EQ_MP (@lem4434797 A K k x' x h1 h2) (@lem4433257 A K k x' x h2)). Qed.
Lemma lem4434799 {A K : Type'} (x' : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term143 A K k x' x.
Proof. exact (fun h0 : term144 A K k x' x => @lem4434798 A K k x' x h1 h0). Qed.
Lemma lem4434800 {A K : Type'} (x' : K -> A) (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : (term113 A K k x' x) = (term124 A K x' x).
Proof. exact (EQ_MP (@lem4433256 A K k x' x) (@lem4434799 A K x' k x h1)). Qed.
Lemma lem4434805 {A K : Type'} (k : K -> Prop) (x : K -> A) (h1 : term82 A K k x) : term126 A K k x.
Proof. exact (fun x' : K -> A => @lem4434800 A K x' k x h1). Qed.
Lemma lem4434806 {A K : Type'} (k : K -> Prop) (x : K -> A) : term127 A K k x.
Proof. exact (fun h0 : term82 A K k x => @lem4434805 A K k x h0). Qed.
Lemma lem4434811 {A K : Type'} (k : K -> Prop) : term129 A K k.
Proof. exact (fun x : K -> A => @lem4434806 A K k x). Qed.
Lemma lem4434816 {A K : Type'} : term131 A K.
Proof. exact (fun k : K -> Prop => @lem4434811 A K k). Qed.
Lemma lem4434817 {A K : Type'} : term133 A K.
Proof. exact (EQ_MP (@lem4433251 A K) (@lem4434816 A K)). Qed.
Lemma lem4434819 {A K : Type'} : term133 A K.
Proof. exact (@lem4433096 A K (@lem4434817 A K)). Qed.
Lemma lem4434820 {A K : Type'} (h1 : term134 A K) : False.
Proof. exact (@lem4434819 A K (@lem4433080 A K h1)). Qed.
Lemma lem4434821 {A K : Type'} (h1 : term134 A K) : (term134 A K) = False.
Proof. exact (prop_ext (fun h2 : term134 A K => @lem4434820 A K h1) (fun h2 : False => @lem4433080 A K h1)). Qed.
Lemma lem4434822 {A K : Type'} (h1 : term134 A K) : False.
Proof. exact (EQ_MP (@lem4434821 A K h1) (@lem4433080 A K h1)). Qed.
Lemma lem4434823 {A K : Type'} : term133 A K.
Proof. exact (fun h0 : term134 A K => @lem4434822 A K h0). Qed.
Lemma lem4434824 {A K : Type'} : term131 A K.
Proof. exact (EQ_MP (@lem4433079 A K) (@lem4434823 A K)). Qed.
Lemma lem4434825 {A K : Type'} : term123 A K.
Proof. exact (EQ_MP (@lem4433075 A K) (@lem4434824 A K)). Qed.
Lemma lem4434826 {A K : Type'} : term75 A K.
Proof. exact (EQ_MP (@lem4432979 A K) (@lem4434825 A K)). Qed.
Lemma lem4434827 {A K : Type'} : term74 A K.
Proof. exact (EQ_MP (@lem4432765 A K) (@lem4434826 A K)). Qed.
