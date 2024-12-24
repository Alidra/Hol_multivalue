Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_SWAP_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_EQ_NEUTRAL_spec.
Require Import ITERATE_OP_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem6017765 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (h1 : (term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g)) : (term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g).
Proof. exact (h1). Qed.
Lemma lem6017766 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (s : _122572 -> Prop) (g : _122572 -> _122573) (h1 : (term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g)) : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g).
Proof. exact (SYM (@lem6017765 _122572 _122573 f op s g h1)). Qed.
Lemma lem6017767 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (h1 : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g)) : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g).
Proof. exact (h1). Qed.
Lemma lem6017768 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (h1 : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g)) : (term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g).
Proof. exact (SYM (@lem6017767 _122572 _122573 s op f g h1)). Qed.
Lemma lem6017769 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : ((term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g)) = ((term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g)).
Proof. exact (prop_ext (fun h1 : (term0 _122572 _122573 s op f g) = (term1 _122572 _122573 f op s g) => @lem6017766 _122572 _122573 f op s g h1) (fun h1 : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g) => @lem6017768 _122572 _122573 s op f g h1)). Qed.
Lemma lem6017770 {_122572 : Type'} (s : _122572 -> Prop) : (term2 _122572 s) = (term2 _122572 s).
Proof. exact (eq_refl (term2 _122572 s)). Qed.
Lemma lem6017771 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term3 _122572 _122573 f op s g) = (term4 _122572 _122573 s op f g).
Proof. exact (MK_COMB (@lem6017770 _122572 s) (@lem6017769 _122572 _122573 s op f g)). Qed.
Lemma lem6017772 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term5 _122572 _122573 f op g) = (term6 _122572 _122573 op f g).
Proof. exact (fun_ext (fun s : _122572 -> Prop => @lem6017771 _122572 _122573 s op f g)). Qed.
Lemma lem6017773 {_122572 : Type'} : (@all (_122572 -> Prop)) = (@all (_122572 -> Prop)).
Proof. exact (eq_refl (@all (_122572 -> Prop))). Qed.
Lemma lem6017774 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term7 _122572 _122573 f op g) = (term8 _122572 _122573 op f g).
Proof. exact (MK_COMB (@lem6017773 _122572) (@lem6017772 _122572 _122573 op f g)). Qed.
Lemma lem6017775 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) : (term9 _122572 _122573 f op) = (term10 _122572 _122573 op f).
Proof. exact (fun_ext (fun g : _122572 -> _122573 => @lem6017774 _122572 _122573 op f g)). Qed.
Lemma lem6017776 {_122572 _122573 : Type'} : (@all (_122572 -> _122573)) = (@all (_122572 -> _122573)).
Proof. exact (eq_refl (@all (_122572 -> _122573))). Qed.
Lemma lem6017777 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) : (term11 _122572 _122573 f op) = (term12 _122572 _122573 op f).
Proof. exact (MK_COMB (@lem6017776 _122572 _122573) (@lem6017775 _122572 _122573 op f)). Qed.
Lemma lem6017778 {_122572 _122573 : Type'} (op : type1400 _122573) : (term13 _122572 _122573 op) = (term14 _122572 _122573 op).
Proof. exact (fun_ext (fun f : _122572 -> _122573 => @lem6017777 _122572 _122573 op f)). Qed.
Lemma lem6017779 {_122572 _122573 : Type'} : (@all (_122572 -> _122573)) = (@all (_122572 -> _122573)).
Proof. exact (eq_refl (@all (_122572 -> _122573))). Qed.
Lemma lem6017780 {_122572 _122573 : Type'} (op : type1400 _122573) : (term15 _122572 _122573 op) = (term16 _122572 _122573 op).
Proof. exact (MK_COMB (@lem6017779 _122572 _122573) (@lem6017778 _122572 _122573 op)). Qed.
Lemma lem6017781 {_122573 : Type'} (op : type1400 _122573) : (term17 _122573 op) = (term17 _122573 op).
Proof. exact (eq_refl (term17 _122573 op)). Qed.
Lemma lem6017782 {_122572 _122573 : Type'} (op : type1400 _122573) : (term18 _122572 _122573 op) = (term19 _122572 _122573 op).
Proof. exact (MK_COMB (@lem6017781 _122573 op) (@lem6017780 _122572 _122573 op)). Qed.
Lemma lem6017783 {_122572 _122573 : Type'} : (term20 _122572 _122573) = (term21 _122572 _122573).
Proof. exact (fun_ext (fun op : type1400 _122573 => @lem6017782 _122572 _122573 op)). Qed.
Lemma lem6017784 {_122573 : Type'} : (@all (_122573 -> _122573 -> _122573)) = (@all (_122573 -> _122573 -> _122573)).
Proof. exact (eq_refl (@all (_122573 -> _122573 -> _122573))). Qed.
Lemma lem6017785 {_122572 _122573 : Type'} : (term22 _122572 _122573) = (term23 _122572 _122573).
Proof. exact (MK_COMB (@lem6017784 _122573) (@lem6017783 _122572 _122573)). Qed.
Lemma lem6017786 {_122572 _122573 : Type'} : term23 _122572 _122573.
Proof. exact (EQ_MP (@lem6017785 _122572 _122573) (@lem6013661 _122572 _122573)). Qed.
Lemma lem6017787 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem6017788 {A : Type'} (P : type686 A) (h1 : term24 A) : term25 A P.
Proof. exact (@lem6017787 A h1 P). Qed.
Lemma lem6017789 {A : Type'} (P : type686 A) : (term25 A P) = (term26 A P).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem6017790 {A : Type'} (P : type686 A) (h1 : term24 A) : term26 A P.
Proof. exact (EQ_MP (@lem6017789 A P) (@lem6017788 A P h1)). Qed.
Lemma lem6017791 {A : Type'} (P : type686 A) (h1 : term27 A P) : term27 A P.
Proof. exact (h1). Qed.
Lemma lem6017792 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term27 A P) : term28 A P.
Proof. exact (@lem6017790 A P h1 (@lem6017791 A P h2)). Qed.
Lemma lem6017793 {A : Type'} (P : type686 A) (h1 : term27 A P) : term29 A P.
Proof. exact (fun h0 : term24 A => @lem6017792 A P h0 h1). Qed.
Lemma lem6017794 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem6017795 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term27 A P) : term28 A P.
Proof. exact (@lem6017793 A P h2 (@lem6017794 A h1)). Qed.
Lemma lem6017796 {A : Type'} (P : type686 A) (h1 : term24 A) : term26 A P.
Proof. exact (fun h0 : term27 A P => @lem6017795 A P h1 h0). Qed.
Lemma lem6017797 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (fun P : type686 A => @lem6017796 A P h1). Qed.
Lemma lem6017798 {A : Type'} : term30 A.
Proof. exact (fun h0 : term24 A => @lem6017797 A h0). Qed.
Lemma lem6017799 {A : Type'} : term24 A.
Proof. exact (@lem6017798 A (@lem3558722 A)). Qed.
Lemma lem6017800 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (@lem6017799 A P). Qed.
Lemma lem6017801 {A : Type'} (P : type686 A) : (term25 A P) = (term26 A P).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem6017803 {A : Type'} (P : Prop) : term31 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem6017804 {A : Type'} (P : Prop) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem6017805 {A : Type'} (P : Prop) : term32 A P.
Proof. exact (EQ_MP (@lem6017804 A P) (@lem6017803 A P)). Qed.
Lemma lem6017806 {A : Type'} (P : Prop) (Q : A -> Prop) : term33 A P Q.
Proof. exact (@lem6017805 A P Q). Qed.
Lemma lem6017807 {A : Type'} (P : Prop) (Q : A -> Prop) : (term33 A P Q) = ((term34 A P Q) = (term35 A P Q)).
Proof. exact (eq_refl (term33 A P Q)). Qed.
Lemma lem6017809 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem6017839 (p : Prop) (q : Prop) (r : Prop) : (term36 p q r) = (term37 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem6017840 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term38 A B C t op s f) = (term39 A B C t op s f).
Proof. exact (@lem6017839 (@FINITE A s) (@FINITE B t) ((term40 A B C s op t f) = (term41 A B C t op s f))). Qed.
Lemma lem6017847 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term42 A B C op s f) = (term43 A B C op s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6017840 A B C t op s f)). Qed.
Lemma lem6017848 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6017849 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term44 A B C op s f) = (term45 A B C op s f).
Proof. exact (MK_COMB (@lem6017848 B) (@lem6017847 A B C op s f)). Qed.
Lemma lem6017851 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem6017807 A P Q) (@lem6017806 A P Q)). Qed.
Lemma lem6017852 {B : Type'} (P : Prop) (Q : type686 B) : (term46 B P Q) = (term47 B P Q).
Proof. exact (@lem6017851 (B -> Prop) P Q). Qed.
Lemma lem6017853 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term48 A B C op s f) = (term49 A B C op s f).
Proof. exact (@lem6017852 B (@FINITE A s) (term50 A B C op s f)). Qed.
Lemma lem6017854 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term51 A B C op s f t) = (term52 A B C t op s f).
Proof. exact (eq_refl (term51 A B C op s f t)). Qed.
Lemma lem6017855 {A : Type'} (s : A -> Prop) : (term2 A s) = (term2 A s).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem6017856 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term53 A B C op s f t) = (term39 A B C t op s f).
Proof. exact (MK_COMB (@lem6017855 A s) (@lem6017854 A B C t op s f)). Qed.
Lemma lem6017857 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term54 A B C op s f) = (term43 A B C op s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6017856 A B C t op s f)). Qed.
Lemma lem6017858 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6017859 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term48 A B C op s f) = (term45 A B C op s f).
Proof. exact (MK_COMB (@lem6017858 B) (@lem6017857 A B C op s f)). Qed.
Lemma lem6017860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6017861 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term55 A B C op s f) = (term56 A B C op s f).
Proof. exact (MK_COMB (@lem6017860) (@lem6017859 A B C op s f)). Qed.
Lemma lem6017862 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term51 A B C op s f t) = (term52 A B C t op s f).
Proof. exact (eq_refl (term51 A B C op s f t)). Qed.
Lemma lem6017863 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term57 A B C op s f) = (term50 A B C op s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6017862 A B C t op s f)). Qed.
Lemma lem6017864 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6017865 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term58 A B C op s f) = (term59 A B C op s f).
Proof. exact (MK_COMB (@lem6017864 B) (@lem6017863 A B C op s f)). Qed.
Lemma lem6017866 {A : Type'} (s : A -> Prop) : (term2 A s) = (term2 A s).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem6017867 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term49 A B C op s f) = (term60 A B C op s f).
Proof. exact (MK_COMB (@lem6017866 A s) (@lem6017865 A B C op s f)). Qed.
Lemma lem6017868 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term48 A B C op s f) = (term49 A B C op s f)) = ((term45 A B C op s f) = (term60 A B C op s f)).
Proof. exact (MK_COMB (@lem6017861 A B C op s f) (@lem6017867 A B C op s f)). Qed.
Lemma lem6017869 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term45 A B C op s f) = (term60 A B C op s f).
Proof. exact (EQ_MP (@lem6017868 A B C op s f) (@lem6017853 A B C op s f)). Qed.
Lemma lem6017900 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term44 A B C op s f) = (term60 A B C op s f).
Proof. exact (TRANS (@lem6017849 A B C op s f) (@lem6017869 A B C op s f)). Qed.
Lemma lem6017901 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term61 A B C op f) = (term62 A B C op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017900 A B C op s f)). Qed.
Lemma lem6017902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017903 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term63 A B C op f) = (term64 A B C op f).
Proof. exact (MK_COMB (@lem6017902 A) (@lem6017901 A B C op f)). Qed.
Lemma lem6017928 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term64 A B C op f) = (term63 A B C op f).
Proof. exact (SYM (@lem6017903 A B C op f)). Qed.
Lemma lem6017930 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (EQ_MP (@lem6017801 A P) (@lem6017800 A P)). Qed.
Lemma lem6017931 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem6017930 A P). Qed.
Lemma lem6017932 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : term65 A B C op f.
Proof. exact (@lem6017931 A (term66 A B C op f)). Qed.
Lemma lem6017933 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term67 A B C op f) = (term68 A B C op f).
Proof. exact (eq_refl (term67 A B C op f)). Qed.
Lemma lem6017934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017935 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term69 A B C op f) = (term70 A B C op f).
Proof. exact (MK_COMB (@lem6017934) (@lem6017933 A B C op f)). Qed.
Lemma lem6017936 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term71 A B C op f s) = (term59 A B C op s f).
Proof. exact (eq_refl (term71 A B C op f s)). Qed.
Lemma lem6017937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6017938 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term72 A B C op f s) = (term73 A B C op s f).
Proof. exact (MK_COMB (@lem6017937) (@lem6017936 A B C op s f)). Qed.
Lemma lem6017939 {A : Type'} (x : A) (s : A -> Prop) : (term74 A x s) = (term74 A x s).
Proof. exact (eq_refl (term74 A x s)). Qed.
Lemma lem6017940 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : (term75 A B C op f x s) = (term76 A B C op f x s).
Proof. exact (MK_COMB (@lem6017938 A B C op s f) (@lem6017939 A x s)). Qed.
Lemma lem6017941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017942 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : (term77 A B C op f x s) = (term78 A B C op f x s).
Proof. exact (MK_COMB (@lem6017941) (@lem6017940 A B C op f x s)). Qed.
Lemma lem6017943 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) : (term79 A B C op f x s) = (term80 A B C op x s f).
Proof. exact (eq_refl (term79 A B C op f x s)). Qed.
Lemma lem6017944 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) : (term81 A B C op f x s) = (term82 A B C op x s f).
Proof. exact (MK_COMB (@lem6017942 A B C op f x s) (@lem6017943 A B C op x s f)). Qed.
Lemma lem6017945 {A B C : Type'} (op : type1400 C) (x : A) (f : type1412 A B C) : (term83 A B C op f x) = (term84 A B C op x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017944 A B C op x s f)). Qed.
Lemma lem6017946 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017947 {A B C : Type'} (op : type1400 C) (x : A) (f : type1412 A B C) : (term85 A B C op f x) = (term86 A B C op x f).
Proof. exact (MK_COMB (@lem6017946 A) (@lem6017945 A B C op x f)). Qed.
Lemma lem6017948 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term87 A B C op f) = (term88 A B C op f).
Proof. exact (fun_ext (fun x : A => @lem6017947 A B C op x f)). Qed.
Lemma lem6017949 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6017950 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term89 A B C op f) = (term90 A B C op f).
Proof. exact (MK_COMB (@lem6017949 A) (@lem6017948 A B C op f)). Qed.
Lemma lem6017951 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term91 A B C op f) = (term92 A B C op f).
Proof. exact (MK_COMB (@lem6017935 A B C op f) (@lem6017950 A B C op f)). Qed.
Lemma lem6017952 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6017953 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term93 A B C op f) = (term94 A B C op f).
Proof. exact (MK_COMB (@lem6017952) (@lem6017951 A B C op f)). Qed.
Lemma lem6017954 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term71 A B C op f s) = (term59 A B C op s f).
Proof. exact (eq_refl (term71 A B C op f s)). Qed.
Lemma lem6017955 {A : Type'} (s : A -> Prop) : (term2 A s) = (term2 A s).
Proof. exact (eq_refl (term2 A s)). Qed.
Lemma lem6017956 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term95 A B C op f s) = (term60 A B C op s f).
Proof. exact (MK_COMB (@lem6017955 A s) (@lem6017954 A B C op s f)). Qed.
Lemma lem6017957 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term96 A B C op f) = (term62 A B C op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6017956 A B C op s f)). Qed.
Lemma lem6017958 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6017959 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term97 A B C op f) = (term64 A B C op f).
Proof. exact (MK_COMB (@lem6017958 A) (@lem6017957 A B C op f)). Qed.
Lemma lem6017960 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : (term65 A B C op f) = (term98 A B C op f).
Proof. exact (MK_COMB (@lem6017953 A B C op f) (@lem6017959 A B C op f)). Qed.
Lemma lem6017961 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) : term98 A B C op f.
Proof. exact (EQ_MP (@lem6017960 A B C op f) (@lem6017932 A B C op f)). Qed.
Lemma lem6017962 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term99 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6017963 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term99 _120477 _120519 _120521 op) = (term100 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term99 _120477 _120519 _120521 op)). Qed.
Lemma lem6017964 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term100 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6017963 _120477 _120519 _120521 op) (@lem6017962 _120477 _120519 _120521 op)). Qed.
Lemma lem6017965 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6017966 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term101 _120477 _120519 _120521 op.
Proof. exact (@lem6017964 _120477 _120519 _120521 op (@lem6017965 _120519 op h1)). Qed.
Lemma lem6017967 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term102 _120519 _120521 op.
Proof. exact (proj2 (@lem6017966 Prop _120519 _120521 op h1)). Qed.
Lemma lem6017968 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term103 _120519 _120521 op f.
Proof. exact (@lem6017967 _120519 _120521 op h1 f). Qed.
Lemma lem6017969 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term103 _120519 _120521 op f) = (term104 _120519 _120521 op f).
Proof. exact (eq_refl (term103 _120519 _120521 op f)). Qed.
Lemma lem6017970 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term104 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem6017969 _120519 _120521 op f) (@lem6017968 _120519 _120521 f op h1)). Qed.
Lemma lem6017971 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term105 _120519 _120521 op f x.
Proof. exact (@lem6017970 _120519 _120521 f op h1 x). Qed.
Lemma lem6017972 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term105 _120519 _120521 op f x) = (term106 _120519 _120521 x op f).
Proof. exact (eq_refl (term105 _120519 _120521 op f x)). Qed.
Lemma lem6017973 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term106 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem6017972 _120519 _120521 x op f) (@lem6017971 _120519 _120521 f x op h1)). Qed.
Lemma lem6017974 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term107 _120519 _120521 x op f s.
Proof. exact (@lem6017973 _120519 _120521 x f op h1 s). Qed.
Lemma lem6017975 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term107 _120519 _120521 x op f s) = (term108 _120519 _120521 x op s f).
Proof. exact (eq_refl (term107 _120519 _120521 x op f s)). Qed.
Lemma lem6017976 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term108 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6017975 _120519 _120521 x op s f) (@lem6017974 _120519 _120521 x f s op h1)). Qed.
Lemma lem6017977 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem6017978 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term109 _120519 _120521 op x s f) = (term110 _120519 _120521 x op s f).
Proof. exact (@lem6017976 _120519 _120521 x s f op h2 (@lem6017977 _120521 s h1)). Qed.
Lemma lem6017979 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term111 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6017978 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem6017980 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term112 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem6017979 _120519 _120521 x op f s h0). Qed.
Lemma lem6017982 (p : Prop) (q : Prop) (r : Prop) : (term37 p q r) = (term36 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6017987 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term112 _120519 _120521 x op s f) = (term113 _120519 _120521 x op s f).
Proof. exact (@lem6017982 (@FINITE _120521 s) (@monoidal _120519 op) ((term109 _120519 _120521 op x s f) = (term110 _120519 _120521 x op s f))). Qed.
Lemma lem6017989 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term114 _120477 _120519 op.
Proof. exact (proj1 (@lem6017966 _120477 _120519 Prop op h1)). Qed.
Lemma lem6017990 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term115 _120477 _120519 op f.
Proof. exact (@lem6017989 _120477 _120519 op h1 f). Qed.
Lemma lem6017991 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term115 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term115 _120477 _120519 op f)). Qed.
Lemma lem6017992 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6017991 _120477 _120519 f op) (@lem6017990 _120477 _120519 f op h1)). Qed.
Lemma lem6017998 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem6018009 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6018010 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6018009 p q p' q'). Qed.
Lemma lem6018011 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6018010 p q p'). Qed.
Lemma lem6018012 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) : term119 A B C t op f.
Proof. exact (@lem6018011 (@FINITE B t) ((term120 A B C op t f) = (term121 A B C t op f))). Qed.
Lemma lem6018013 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) : term122 A B C t op f p'.
Proof. exact (@lem6018012 A B C t op f p'). Qed.
Lemma lem6018014 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) : (term122 A B C t op f p') = (term123 A B C t op f p').
Proof. exact (eq_refl (term122 A B C t op f p')). Qed.
Lemma lem6018015 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) : term123 A B C t op f p'.
Proof. exact (EQ_MP (@lem6018014 A B C t op f p') (@lem6018013 A B C t op f p')). Qed.
Lemma lem6018016 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term124 A B C t op f p' q'.
Proof. exact (@lem6018015 A B C t op f p' q'). Qed.
Lemma lem6018017 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term124 A B C t op f p' q') = (term125 A B C t op f p' q').
Proof. exact (eq_refl (term124 A B C t op f p' q')). Qed.
Lemma lem6018018 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term125 A B C t op f p' q'.
Proof. exact (EQ_MP (@lem6018017 A B C t op f p' q') (@lem6018016 A B C t op f p' q')). Qed.
Lemma lem6018019 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6018020 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term126 A B C op f t q'.
Proof. exact (@lem6018018 A B C t op f (@FINITE B t) q'). Qed.
Lemma lem6018021 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term127 A B C op f t q'.
Proof. exact (@lem6018020 A B C op f t q' (@lem6018019 B t)). Qed.
Lemma lem6018028 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term128 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6017992 _120477 _120519 f op h0). Qed.
Lemma lem6018029 {A C : Type'} (f : A -> C) (op : type1400 C) : term128 A C f op.
Proof. exact (@lem6018028 A C f op). Qed.
Lemma lem6018030 {A B C : Type'} (t : B -> Prop) (f : type1412 A B C) (op : type1400 C) : term129 A B C t f op.
Proof. exact (@lem6018029 A C (term130 A B C op t f) op). Qed.
Lemma lem6018032 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6017998 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6018033 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6018032 C op h1)). Qed.
Lemma lem6018034 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6018033 C op h1) (@lem0)). Qed.
Lemma lem6018035 {A B C : Type'} (t : B -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term120 A B C op t f) = (@neutral C op).
Proof. exact (@lem6018030 A B C t f op (@lem6018034 C op h1)). Qed.
Lemma lem6018036 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6018037 {A B C : Type'} (t : B -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term131 A B C op t f) = (term132 C op).
Proof. exact (MK_COMB (@lem6018036 C) (@lem6018035 A B C t f op h1)). Qed.
Lemma lem6018039 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term128 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6017992 _120477 _120519 f op h0). Qed.
Lemma lem6018040 {A C : Type'} (f : A -> C) (op : type1400 C) : term128 A C f op.
Proof. exact (@lem6018039 A C f op). Qed.
Lemma lem6018041 {A B C : Type'} (f : type1412 A B C) (j : B) (op : type1400 C) : term133 A B C f j op.
Proof. exact (@lem6018040 A C (term134 A B C f j) op). Qed.
Lemma lem6018043 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6017998 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6018044 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : True = (@monoidal C op).
Proof. exact (SYM (@lem6018043 C op h1)). Qed.
Lemma lem6018045 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (EQ_MP (@lem6018044 C op h1) (@lem0)). Qed.
Lemma lem6018046 {A B C : Type'} (f : type1412 A B C) (j : B) (op : type1400 C) (h1 : @monoidal C op) : (term135 A B C op f j) = (@neutral C op).
Proof. exact (@lem6018041 A B C f j op (@lem6018045 C op h1)). Qed.
Lemma lem6018047 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term136 A B C op f) = (term137 B C op).
Proof. exact (fun_ext (fun j : B => @lem6018046 A B C f j op h1)). Qed.
Lemma lem6018048 {B C : Type'} (op : type1400 C) (t : B -> Prop) : (@iterate C B op t) = (@iterate C B op t).
Proof. exact (eq_refl (@iterate C B op t)). Qed.
Lemma lem6018049 {A B C : Type'} (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term121 A B C t op f) = (term138 B C t op).
Proof. exact (MK_COMB (@lem6018048 B C op t) (@lem6018047 A B C f op h1)). Qed.
Lemma lem6018050 {A B C : Type'} (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : ((term120 A B C op t f) = (term121 A B C t op f)) = ((@neutral C op) = (term138 B C t op)).
Proof. exact (MK_COMB (@lem6018037 A B C t f op h1) (@lem6018049 A B C f t op h1)). Qed.
Lemma lem6018053 {A B C : Type'} (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term139 A B C f t op.
Proof. exact (fun h0 : @FINITE B t => @lem6018050 A B C f t op h1). Qed.
Lemma lem6018054 {A B C : Type'} (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) : term140 A B C f t op.
Proof. exact (@lem6018021 A B C op f t ((@neutral C op) = (term138 B C t op))). Qed.
Lemma lem6018055 {A B C : Type'} (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term141 A B C t op f) = (term142 B C t op).
Proof. exact (@lem6018054 A B C f t op (@lem6018053 A B C f t op h1)). Qed.
Lemma lem6018083 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term143 A B C op f) = (term144 B C op).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6018055 A B C f t op h1)). Qed.
Lemma lem6018111 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6018112 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term68 A B C op f) = (term145 B C op).
Proof. exact (MK_COMB (@lem6018111 B) (@lem6018083 A B C f op h1)). Qed.
Lemma lem6018144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6018145 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term70 A B C op f) = (term146 B C op).
Proof. exact (MK_COMB (@lem6018144) (@lem6018112 A B C f op h1)). Qed.
Lemma lem6018188 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6018189 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6018188 p q p' q'). Qed.
Lemma lem6018190 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6018189 p q p'). Qed.
Lemma lem6018191 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) : term147 A B C op x s f.
Proof. exact (@lem6018190 (term76 A B C op f x s) (term80 A B C op x s f)). Qed.
Lemma lem6018192 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term148 A B C op x s f p'.
Proof. exact (@lem6018191 A B C op x s f p'). Qed.
Lemma lem6018193 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : (term148 A B C op x s f p') = (term149 A B C op x s f p').
Proof. exact (eq_refl (term148 A B C op x s f p')). Qed.
Lemma lem6018194 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term149 A B C op x s f p'.
Proof. exact (EQ_MP (@lem6018193 A B C op x s f p') (@lem6018192 A B C op x s f p')). Qed.
Lemma lem6018195 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term150 A B C op x s f p' q'.
Proof. exact (@lem6018194 A B C op x s f p' q'). Qed.
Lemma lem6018196 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term150 A B C op x s f p' q') = (term151 A B C op x s f p' q').
Proof. exact (eq_refl (term150 A B C op x s f p' q')). Qed.
Lemma lem6018197 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term151 A B C op x s f p' q'.
Proof. exact (EQ_MP (@lem6018196 A B C op x s f p' q') (@lem6018195 A B C op x s f p' q')). Qed.
Lemma lem6018233 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : (term76 A B C op f x s) = (term76 A B C op f x s).
Proof. exact (eq_refl (term76 A B C op f x s)). Qed.
Lemma lem6018234 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (q' : Prop) : term152 A B C op f x s q'.
Proof. exact (@lem6018197 A B C op x s f (term76 A B C op f x s) q'). Qed.
Lemma lem6018235 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (q' : Prop) : term153 A B C op f x s q'.
Proof. exact (@lem6018234 A B C op f x s q' (@lem6018233 A B C op f x s)). Qed.
Lemma lem6018236 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term76 A B C op f x s.
Proof. exact (h1). Qed.
Lemma lem6018237 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term74 A x s.
Proof. exact (proj2 (@lem6018236 A B C op f x s h1)). Qed.
Lemma lem6018238 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : @FINITE A s.
Proof. exact (proj2 (@lem6018237 A B C op f x s h1)). Qed.
Lemma lem6018239 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6018241 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term154 A x s.
Proof. exact (proj1 (@lem6018237 A B C op f x s h1)). Qed.
Lemma lem6018242 {A : Type'} (x : A) (s : A -> Prop) : term155 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem6018244 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term59 A B C op s f.
Proof. exact (proj1 (@lem6018236 A B C op f x s h1)). Qed.
Lemma lem6018245 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term51 A B C op s f t.
Proof. exact (@lem6018244 A B C op f x s h1 t). Qed.
Lemma lem6018246 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term51 A B C op s f t) = (term52 A B C t op s f).
Proof. exact (eq_refl (term51 A B C op s f t)). Qed.
Lemma lem6018247 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term52 A B C t op s f.
Proof. exact (EQ_MP (@lem6018246 A B C t op s f) (@lem6018245 A B C t op f x s h1)). Qed.
Lemma lem6018248 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6018249 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term40 A B C s op t f) = (term41 A B C t op s f).
Proof. exact (@lem6018247 A B C t op f x s h2 (@lem6018248 B t h1)). Qed.
Lemma lem6018262 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6018263 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6018262 p q p' q'). Qed.
Lemma lem6018264 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6018263 p q p'). Qed.
Lemma lem6018265 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) : term156 A B C t op x s f.
Proof. exact (@lem6018264 (@FINITE B t) ((term157 A B C x s op t f) = (term158 A B C t op x s f))). Qed.
Lemma lem6018266 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term159 A B C t op x s f p'.
Proof. exact (@lem6018265 A B C t op x s f p'). Qed.
Lemma lem6018267 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : (term159 A B C t op x s f p') = (term160 A B C t op x s f p').
Proof. exact (eq_refl (term159 A B C t op x s f p')). Qed.
Lemma lem6018268 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term160 A B C t op x s f p'.
Proof. exact (EQ_MP (@lem6018267 A B C t op x s f p') (@lem6018266 A B C t op x s f p')). Qed.
Lemma lem6018269 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term161 A B C t op x s f p' q'.
Proof. exact (@lem6018268 A B C t op x s f p' q'). Qed.
Lemma lem6018270 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term161 A B C t op x s f p' q') = (term162 A B C t op x s f p' q').
Proof. exact (eq_refl (term161 A B C t op x s f p' q')). Qed.
Lemma lem6018271 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term162 A B C t op x s f p' q'.
Proof. exact (EQ_MP (@lem6018270 A B C t op x s f p' q') (@lem6018269 A B C t op x s f p' q')). Qed.
Lemma lem6018272 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6018273 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term163 A B C op x s f t q'.
Proof. exact (@lem6018271 A B C t op x s f (@FINITE B t) q'). Qed.
Lemma lem6018274 {A B C : Type'} (op : type1400 C) (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term164 A B C op x s f t q'.
Proof. exact (@lem6018273 A B C op x s f t q' (@lem6018272 B t)). Qed.
Lemma lem6018275 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6018276 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6018281 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term113 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6017987 _120519 _120521 x op s f) (@lem6017980 _120519 _120521 x op s f)). Qed.
Lemma lem6018282 {A C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : A -> C) : term165 A C x op s f.
Proof. exact (@lem6018281 C A x op s f). Qed.
Lemma lem6018283 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) : term166 A B C x s op t f.
Proof. exact (@lem6018282 A C x op s (term130 A B C op t f)). Qed.
Lemma lem6018287 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6018239 A s) (@lem6018238 A B C op f x s h1)). Qed.
Lemma lem6018288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6018289 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (term167 A s) = (and True).
Proof. exact (MK_COMB (@lem6018288) (@lem6018287 A B C op f x s h1)). Qed.
Lemma lem6018291 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6017998 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6018292 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term168 A C s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6018289 A B C op f x s h2) (@lem6018291 C op h1)). Qed.
Lemma lem6018294 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6018295 : (True /\ True) = True.
Proof. exact (@lem6018294 True). Qed.
Lemma lem6018296 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term168 A C s op) = True.
Proof. exact (TRANS (@lem6018292 A B C op f x s h1 h2) (@lem6018295)). Qed.
Lemma lem6018297 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : True = (term168 A C s op).
Proof. exact (SYM (@lem6018296 A B C op f x s h1 h2)). Qed.
Lemma lem6018298 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : term168 A C s op.
Proof. exact (EQ_MP (@lem6018297 A B C op f x s h1 h2) (@lem0)). Qed.
Lemma lem6018299 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term157 A B C x s op t f) = (term169 A B C x s op t f).
Proof. exact (@lem6018283 A B C x s op t f (@lem6018298 A B C op f x s h1 h2)). Qed.
Lemma lem6018301 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term170 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6018302 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term171 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6018301 _2963 g t e g' t' e'). Qed.
Lemma lem6018303 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term172 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6018302 _2963 g t e g' t'). Qed.
Lemma lem6018304 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term173 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6018303 _2963 g t e g'). Qed.
Lemma lem6018305 {C : Type'} (g : Prop) (t : C) (e : C) : term173 C g t e.
Proof. exact (@lem6018304 C g t e). Qed.
Lemma lem6018306 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) : term174 A B C x s op t f.
Proof. exact (@lem6018305 C (@IN A x s) (term40 A B C s op t f) (term175 A B C x s op t f)). Qed.
Lemma lem6018307 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) : term176 A B C x s op t f g'.
Proof. exact (@lem6018306 A B C x s op t f g'). Qed.
Lemma lem6018308 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) : (term176 A B C x s op t f g') = (term177 A B C x s op t f g').
Proof. exact (eq_refl (term176 A B C x s op t f g')). Qed.
Lemma lem6018309 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) : term177 A B C x s op t f g'.
Proof. exact (EQ_MP (@lem6018308 A B C x s op t f g') (@lem6018307 A B C x s op t f g')). Qed.
Lemma lem6018310 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) : term178 A B C x s op t f g' t'.
Proof. exact (@lem6018309 A B C x s op t f g' t'). Qed.
Lemma lem6018311 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) : (term178 A B C x s op t f g' t') = (term179 A B C x s op t f g' t').
Proof. exact (eq_refl (term178 A B C x s op t f g' t')). Qed.
Lemma lem6018312 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) : term179 A B C x s op t f g' t'.
Proof. exact (EQ_MP (@lem6018311 A B C x s op t f g' t') (@lem6018310 A B C x s op t f g' t')). Qed.
Lemma lem6018313 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : term180 A B C x s op t f g' t' e'.
Proof. exact (@lem6018312 A B C x s op t f g' t' e'). Qed.
Lemma lem6018314 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : (term180 A B C x s op t f g' t' e') = (term181 A B C x s op t f g' t' e').
Proof. exact (eq_refl (term180 A B C x s op t f g' t' e')). Qed.
Lemma lem6018315 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (g' : Prop) (t' : C) (e' : C) : term181 A B C x s op t f g' t' e'.
Proof. exact (EQ_MP (@lem6018314 A B C x s op t f g' t' e') (@lem6018313 A B C x s op t f g' t' e')). Qed.
Lemma lem6018317 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (@IN A x s) = False.
Proof. exact (@lem6018242 A x s (@lem6018241 A B C op f x s h1)). Qed.
Lemma lem6018318 {A B C : Type'} (x : A) (s : A -> Prop) (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (t' : C) (e' : C) : term182 A B C x s op t f t' e'.
Proof. exact (@lem6018315 A B C x s op t f False t' e'). Qed.
Lemma lem6018319 {A B C : Type'} (t : B -> Prop) (t' : C) (e' : C) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term183 A B C x s op t f t' e'.
Proof. exact (@lem6018318 A B C x s op t f t' e' (@lem6018317 A B C op f x s h1)). Qed.
Lemma lem6018324 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term52 A B C t op s f.
Proof. exact (fun h0 : @FINITE B t => @lem6018249 A B C t op f x s h0 h1). Qed.
Lemma lem6018325 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term52 A B C t op s f.
Proof. exact (@lem6018324 A B C t op f x s h1). Qed.
Lemma lem6018327 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6018276 B t) (@lem6018275 B t h1)). Qed.
Lemma lem6018328 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6018327 B t h1)). Qed.
Lemma lem6018329 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6018328 B t h1) (@lem0)). Qed.
Lemma lem6018330 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term40 A B C s op t f) = (term41 A B C t op s f).
Proof. exact (@lem6018325 A B C t op f x s h2 (@lem6018329 B t h1)). Qed.
Lemma lem6018331 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : term184 A B C t op s f.
Proof. exact (fun h0 : False => @lem6018330 A B C t op f x s h1 h2). Qed.
Lemma lem6018332 {A B C : Type'} (t : B -> Prop) (e' : C) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term185 A B C x t op s f e'.
Proof. exact (@lem6018319 A B C t (term41 A B C t op s f) e' op f x s h1). Qed.
Lemma lem6018333 {A B C : Type'} (e' : C) (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : term186 A B C x t op s f e'.
Proof. exact (@lem6018332 A B C t e' op f x s h2 (@lem6018331 A B C t op f x s h1 h2)). Qed.
Lemma lem6018340 {A B : Type'} (f : A -> B) (y : A) : (term187 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6018341 {A C : Type'} (f : A -> C) (y : A) : (term187 A C f y) = (f y).
Proof. exact (@lem6018340 A C f y). Qed.
Lemma lem6018342 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term188 A B C op t f x) = (term189 A B C op t f x).
Proof. exact (@lem6018341 A C (term130 A B C op t f) x). Qed.
Lemma lem6018343 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (i : A) : (term189 A B C op t f i) = (term190 A B C op t f i).
Proof. exact (eq_refl (term189 A B C op t f i)). Qed.
Lemma lem6018344 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) : (term191 A B C op t f) = (term130 A B C op t f).
Proof. exact (fun_ext (fun i : A => @lem6018343 A B C op t f i)). Qed.
Lemma lem6018345 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6018346 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term188 A B C op t f x) = (term189 A B C op t f x).
Proof. exact (MK_COMB (@lem6018344 A B C op t f) (@lem6018345 A x)). Qed.
Lemma lem6018347 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6018348 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term192 A B C op t f x) = (term193 A B C op t f x).
Proof. exact (MK_COMB (@lem6018347 C) (@lem6018346 A B C op t f x)). Qed.
Lemma lem6018349 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term189 A B C op t f x) = (term190 A B C op t f x).
Proof. exact (eq_refl (term189 A B C op t f x)). Qed.
Lemma lem6018350 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : ((term188 A B C op t f x) = (term189 A B C op t f x)) = ((term189 A B C op t f x) = (term190 A B C op t f x)).
Proof. exact (MK_COMB (@lem6018348 A B C op t f x) (@lem6018349 A B C op t f x)). Qed.
Lemma lem6018351 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term189 A B C op t f x) = (term190 A B C op t f x).
Proof. exact (EQ_MP (@lem6018350 A B C op t f x) (@lem6018342 A B C op t f x)). Qed.
Lemma lem6018352 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6018353 {A B C : Type'} (op : type1400 C) (t : B -> Prop) (f : type1412 A B C) (x : A) : (term194 A B C op t f x) = (term195 A B C op t f x).
Proof. exact (MK_COMB (@lem6018352 C op) (@lem6018351 A B C op t f x)). Qed.
Lemma lem6018355 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term52 A B C t op s f.
Proof. exact (fun h0 : @FINITE B t => @lem6018249 A B C t op f x s h0 h1). Qed.
Lemma lem6018356 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term52 A B C t op s f.
Proof. exact (@lem6018355 A B C t op f x s h1). Qed.
Lemma lem6018358 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6018276 B t) (@lem6018275 B t h1)). Qed.
Lemma lem6018359 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem6018358 B t h1)). Qed.
Lemma lem6018360 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem6018359 B t h1) (@lem0)). Qed.
Lemma lem6018361 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term40 A B C s op t f) = (term41 A B C t op s f).
Proof. exact (@lem6018356 A B C t op f x s h2 (@lem6018360 B t h1)). Qed.
Lemma lem6018362 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term175 A B C x s op t f) = (term196 A B C x t op s f).
Proof. exact (MK_COMB (@lem6018353 A B C op t f x) (@lem6018361 A B C t op f x s h1 h2)). Qed.
Lemma lem6018363 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : term197 A B C x t op s f.
Proof. exact (fun h0 : ~ False => @lem6018362 A B C t op f x s h1 h2). Qed.
Lemma lem6018364 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : term198 A B C x t op s f.
Proof. exact (@lem6018333 A B C (term196 A B C x t op s f) t op f x s h1 h2). Qed.
Lemma lem6018365 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term169 A B C x s op t f) = (term199 A B C x t op s f).
Proof. exact (@lem6018364 A B C t op f x s h1 h2 (@lem6018363 A B C t op f x s h1 h2)). Qed.
Lemma lem6018367 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6018368 {C : Type'} (t1 : C) (t2 : C) : (@COND C False t1 t2) = t2.
Proof. exact (@lem6018367 C t1 t2). Qed.
Lemma lem6018369 {A B C : Type'} (x : A) (t : B -> Prop) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term199 A B C x t op s f) = (term196 A B C x t op s f).
Proof. exact (@lem6018368 C (term41 A B C t op s f) (term196 A B C x t op s f)). Qed.
Lemma lem6018370 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term76 A B C op f x s) : (term169 A B C x s op t f) = (term196 A B C x t op s f).
Proof. exact (TRANS (@lem6018365 A B C t op f x s h1 h2) (@lem6018369 A B C x t op s f)). Qed.
Lemma lem6018371 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : @monoidal C op) (h3 : term76 A B C op f x s) : (term157 A B C x s op t f) = (term196 A B C x t op s f).
Proof. exact (TRANS (@lem6018299 A B C t op f x s h2 h3) (@lem6018370 A B C t op f x s h1 h3)). Qed.
Lemma lem6018372 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6018373 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : @monoidal C op) (h3 : term76 A B C op f x s) : (term200 A B C x s op t f) = (term201 A B C x t op s f).
Proof. exact (MK_COMB (@lem6018372 C) (@lem6018371 A B C t op f x s h1 h2 h3)). Qed.
Lemma lem6018375 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term113 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem6017987 _120519 _120521 x op s f) (@lem6017980 _120519 _120521 x op s f)). Qed.
Lemma lem6018376 {A C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : A -> C) : term165 A C x op s f.
Proof. exact (@lem6018375 C A x op s f). Qed.
Lemma lem6018377 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : term202 A B C x op s f j.
Proof. exact (@lem6018376 A C x op s (term134 A B C f j)). Qed.
Lemma lem6018381 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6018239 A s) (@lem6018238 A B C op f x s h1)). Qed.
Lemma lem6018382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6018383 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (term167 A s) = (and True).
Proof. exact (MK_COMB (@lem6018382) (@lem6018381 A B C op f x s h1)). Qed.
Lemma lem6018385 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6017998 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6018386 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term168 A C s op) = (True /\ True).
Proof. exact (MK_COMB (@lem6018383 A B C op f x s h2) (@lem6018385 C op h1)). Qed.
Lemma lem6018388 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6018389 : (True /\ True) = True.
Proof. exact (@lem6018388 True). Qed.
Lemma lem6018390 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term168 A C s op) = True.
Proof. exact (TRANS (@lem6018386 A B C op f x s h1 h2) (@lem6018389)). Qed.
Lemma lem6018391 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : True = (term168 A C s op).
Proof. exact (SYM (@lem6018390 A B C op f x s h1 h2)). Qed.
Lemma lem6018392 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : term168 A C s op.
Proof. exact (EQ_MP (@lem6018391 A B C op f x s h1 h2) (@lem0)). Qed.
Lemma lem6018393 {A B C : Type'} (j : B) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term203 A B C op x s f j) = (term204 A B C x op s f j).
Proof. exact (@lem6018377 A B C x op s f j (@lem6018392 A B C op f x s h1 h2)). Qed.
Lemma lem6018395 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term170 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6018396 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term171 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6018395 _2963 g t e g' t' e'). Qed.
Lemma lem6018397 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term172 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6018396 _2963 g t e g' t'). Qed.
Lemma lem6018398 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term173 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6018397 _2963 g t e g'). Qed.
Lemma lem6018399 {C : Type'} (g : Prop) (t : C) (e : C) : term173 C g t e.
Proof. exact (@lem6018398 C g t e). Qed.
Lemma lem6018400 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : term205 A B C x op s f j.
Proof. exact (@lem6018399 C (@IN A x s) (term206 A B C op s f j) (term207 A B C x op s f j)). Qed.
Lemma lem6018401 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) : term208 A B C x op s f j g'.
Proof. exact (@lem6018400 A B C x op s f j g'). Qed.
Lemma lem6018402 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) : (term208 A B C x op s f j g') = (term209 A B C x op s f j g').
Proof. exact (eq_refl (term208 A B C x op s f j g')). Qed.
Lemma lem6018403 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) : term209 A B C x op s f j g'.
Proof. exact (EQ_MP (@lem6018402 A B C x op s f j g') (@lem6018401 A B C x op s f j g')). Qed.
Lemma lem6018404 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) : term210 A B C x op s f j g' t'.
Proof. exact (@lem6018403 A B C x op s f j g' t'). Qed.
Lemma lem6018405 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) : (term210 A B C x op s f j g' t') = (term211 A B C x op s f j g' t').
Proof. exact (eq_refl (term210 A B C x op s f j g' t')). Qed.
Lemma lem6018406 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) : term211 A B C x op s f j g' t'.
Proof. exact (EQ_MP (@lem6018405 A B C x op s f j g' t') (@lem6018404 A B C x op s f j g' t')). Qed.
Lemma lem6018407 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) (e' : C) : term212 A B C x op s f j g' t' e'.
Proof. exact (@lem6018406 A B C x op s f j g' t' e'). Qed.
Lemma lem6018408 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) (e' : C) : (term212 A B C x op s f j g' t' e') = (term213 A B C x op s f j g' t' e').
Proof. exact (eq_refl (term212 A B C x op s f j g' t' e')). Qed.
Lemma lem6018409 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (g' : Prop) (t' : C) (e' : C) : term213 A B C x op s f j g' t' e'.
Proof. exact (EQ_MP (@lem6018408 A B C x op s f j g' t' e') (@lem6018407 A B C x op s f j g' t' e')). Qed.
Lemma lem6018411 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (@IN A x s) = False.
Proof. exact (@lem6018242 A x s (@lem6018241 A B C op f x s h1)). Qed.
Lemma lem6018412 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) (t' : C) (e' : C) : term214 A B C x op s f j t' e'.
Proof. exact (@lem6018409 A B C x op s f j False t' e'). Qed.
Lemma lem6018413 {A B C : Type'} (j : B) (t' : C) (e' : C) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term215 A B C x op s f j t' e'.
Proof. exact (@lem6018412 A B C x op s f j t' e' (@lem6018411 A B C op f x s h1)). Qed.
Lemma lem6018417 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : (term206 A B C op s f j) = (term206 A B C op s f j).
Proof. exact (eq_refl (term206 A B C op s f j)). Qed.
Lemma lem6018418 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : term216 A B C op s f j.
Proof. exact (fun h0 : False => @lem6018417 A B C op s f j). Qed.
Lemma lem6018419 {A B C : Type'} (j : B) (e' : C) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term217 A B C x op s f j e'.
Proof. exact (@lem6018413 A B C j (term206 A B C op s f j) e' op f x s h1). Qed.
Lemma lem6018420 {A B C : Type'} (j : B) (e' : C) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term218 A B C x op s f j e'.
Proof. exact (@lem6018419 A B C j e' op f x s h1 (@lem6018418 A B C op s f j)). Qed.
Lemma lem6018427 {A B : Type'} (f : A -> B) (y : A) : (term187 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6018428 {A C : Type'} (f : A -> C) (y : A) : (term187 A C f y) = (f y).
Proof. exact (@lem6018427 A C f y). Qed.
Lemma lem6018429 {A B C : Type'} (f : type1412 A B C) (j : B) (x : A) : (term219 A B C f j x) = (term220 A B C f j x).
Proof. exact (@lem6018428 A C (term134 A B C f j) x). Qed.
Lemma lem6018430 {A B C : Type'} (f : type1412 A B C) (i : A) (j : B) : (term220 A B C f j i) = (f i j).
Proof. exact (eq_refl (term220 A B C f j i)). Qed.
Lemma lem6018431 {A B C : Type'} (f : type1412 A B C) (j : B) : (term221 A B C f j) = (term134 A B C f j).
Proof. exact (fun_ext (fun i : A => @lem6018430 A B C f i j)). Qed.
Lemma lem6018432 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6018433 {A B C : Type'} (f : type1412 A B C) (j : B) (x : A) : (term219 A B C f j x) = (term220 A B C f j x).
Proof. exact (MK_COMB (@lem6018431 A B C f j) (@lem6018432 A x)). Qed.
Lemma lem6018434 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6018435 {A B C : Type'} (f : type1412 A B C) (j : B) (x : A) : (term222 A B C f j x) = (term223 A B C f j x).
Proof. exact (MK_COMB (@lem6018434 C) (@lem6018433 A B C f j x)). Qed.
Lemma lem6018436 {A B C : Type'} (f : type1412 A B C) (x : A) (j : B) : (term220 A B C f j x) = (f x j).
Proof. exact (eq_refl (term220 A B C f j x)). Qed.
Lemma lem6018437 {A B C : Type'} (f : type1412 A B C) (x : A) (j : B) : ((term219 A B C f j x) = (term220 A B C f j x)) = ((term220 A B C f j x) = (f x j)).
Proof. exact (MK_COMB (@lem6018435 A B C f j x) (@lem6018436 A B C f x j)). Qed.
Lemma lem6018438 {A B C : Type'} (f : type1412 A B C) (x : A) (j : B) : (term220 A B C f j x) = (f x j).
Proof. exact (EQ_MP (@lem6018437 A B C f x j) (@lem6018429 A B C f j x)). Qed.
Lemma lem6018439 {C : Type'} (op : type1400 C) : op = op.
Proof. exact (eq_refl op). Qed.
Lemma lem6018440 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (j : B) : (term224 A B C op f j x) = (term225 A B C op f x j).
Proof. exact (MK_COMB (@lem6018439 C op) (@lem6018438 A B C f x j)). Qed.
Lemma lem6018441 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : (term206 A B C op s f j) = (term206 A B C op s f j).
Proof. exact (eq_refl (term206 A B C op s f j)). Qed.
Lemma lem6018442 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : (term207 A B C x op s f j) = (term226 A B C x op s f j).
Proof. exact (MK_COMB (@lem6018440 A B C op f x j) (@lem6018441 A B C op s f j)). Qed.
Lemma lem6018443 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : term227 A B C x op s f j.
Proof. exact (fun h0 : ~ False => @lem6018442 A B C x op s f j). Qed.
Lemma lem6018444 {A B C : Type'} (j : B) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : term228 A B C x op s f j.
Proof. exact (@lem6018420 A B C j (term226 A B C x op s f j) op f x s h1). Qed.
Lemma lem6018445 {A B C : Type'} (j : B) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (term204 A B C x op s f j) = (term229 A B C x op s f j).
Proof. exact (@lem6018444 A B C j op f x s h1 (@lem6018443 A B C x op s f j)). Qed.
Lemma lem6018447 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6018448 {C : Type'} (t1 : C) (t2 : C) : (@COND C False t1 t2) = t2.
Proof. exact (@lem6018447 C t1 t2). Qed.
Lemma lem6018449 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : (term229 A B C x op s f j) = (term226 A B C x op s f j).
Proof. exact (@lem6018448 C (term206 A B C op s f j) (term226 A B C x op s f j)). Qed.
Lemma lem6018450 {A B C : Type'} (j : B) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : term76 A B C op f x s) : (term204 A B C x op s f j) = (term226 A B C x op s f j).
Proof. exact (TRANS (@lem6018445 A B C j op f x s h1) (@lem6018449 A B C x op s f j)). Qed.
Lemma lem6018451 {A B C : Type'} (j : B) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term203 A B C op x s f j) = (term226 A B C x op s f j).
Proof. exact (TRANS (@lem6018393 A B C j op f x s h1 h2) (@lem6018450 A B C j op f x s h2)). Qed.
Lemma lem6018452 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term230 A B C op x s f) = (term231 A B C x op s f).
Proof. exact (fun_ext (fun j : B => @lem6018451 A B C j op f x s h1 h2)). Qed.
Lemma lem6018453 {B C : Type'} (op : type1400 C) (t : B -> Prop) : (@iterate C B op t) = (@iterate C B op t).
Proof. exact (eq_refl (@iterate C B op t)). Qed.
Lemma lem6018454 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term158 A B C t op x s f) = (term232 A B C t x op s f).
Proof. exact (MK_COMB (@lem6018453 B C op t) (@lem6018452 A B C op f x s h1 h2)). Qed.
Lemma lem6018455 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : @monoidal C op) (h3 : term76 A B C op f x s) : ((term157 A B C x s op t f) = (term158 A B C t op x s f)) = ((term196 A B C x t op s f) = (term232 A B C t x op s f)).
Proof. exact (MK_COMB (@lem6018373 A B C t op f x s h1 h2 h3) (@lem6018454 A B C t op f x s h2 h3)). Qed.
Lemma lem6018458 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : term233 A B C t x op s f.
Proof. exact (fun h0 : @FINITE B t => @lem6018455 A B C t op f x s h0 h1 h2). Qed.
Lemma lem6018459 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : term234 A B C t x op s f.
Proof. exact (@lem6018274 A B C op x s f t ((term196 A B C x t op s f) = (term232 A B C t x op s f))). Qed.
Lemma lem6018460 {A B C : Type'} (t : B -> Prop) (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term235 A B C t op x s f) = (term236 A B C t x op s f).
Proof. exact (@lem6018459 A B C t x op s f (@lem6018458 A B C t op f x s h1 h2)). Qed.
Lemma lem6018488 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term237 A B C op x s f) = (term238 A B C x op s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6018460 A B C t op f x s h1 h2)). Qed.
Lemma lem6018516 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6018517 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (h1 : @monoidal C op) (h2 : term76 A B C op f x s) : (term80 A B C op x s f) = (term239 A B C x op s f).
Proof. exact (MK_COMB (@lem6018516 B) (@lem6018488 A B C op f x s h1 h2)). Qed.
Lemma lem6018549 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term240 A B C x op s f.
Proof. exact (fun h0 : term76 A B C op f x s => @lem6018517 A B C op f x s h1 h0). Qed.
Lemma lem6018550 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : term241 A B C x op s f.
Proof. exact (@lem6018235 A B C op f x s (term239 A B C x op s f)). Qed.
Lemma lem6018551 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term82 A B C op x s f) = (term242 A B C x op s f).
Proof. exact (@lem6018550 A B C x op s f (@lem6018549 A B C x s f op h1)). Qed.
Lemma lem6018723 {A B C : Type'} (x : A) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term84 A B C op x f) = (term243 A B C x op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6018551 A B C x s f op h1)). Qed.
Lemma lem6018895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6018896 {A B C : Type'} (x : A) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term86 A B C op x f) = (term244 A B C x op f).
Proof. exact (MK_COMB (@lem6018895 A) (@lem6018723 A B C x f op h1)). Qed.
Lemma lem6019072 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term88 A B C op f) = (term245 A B C op f).
Proof. exact (fun_ext (fun x : A => @lem6018896 A B C x f op h1)). Qed.
Lemma lem6019248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6019249 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term90 A B C op f) = (term246 A B C op f).
Proof. exact (MK_COMB (@lem6019248 A) (@lem6019072 A B C f op h1)). Qed.
Lemma lem6019429 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term92 A B C op f) = (term247 A B C op f).
Proof. exact (MK_COMB (@lem6018145 A B C f op h1) (@lem6019249 A B C f op h1)). Qed.
Lemma lem6019642 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term247 A B C op f) = (term92 A B C op f).
Proof. exact (SYM (@lem6019429 A B C f op h1)). Qed.
Lemma lem6019643 {_122572 _122573 : Type'} (op : type1400 _122573) : term248 _122572 _122573 op.
Proof. exact (@lem6017786 _122572 _122573 op). Qed.
Lemma lem6019644 {_122572 _122573 : Type'} (op : type1400 _122573) : (term248 _122572 _122573 op) = (term19 _122572 _122573 op).
Proof. exact (eq_refl (term248 _122572 _122573 op)). Qed.
Lemma lem6019645 {_122572 _122573 : Type'} (op : type1400 _122573) : term19 _122572 _122573 op.
Proof. exact (EQ_MP (@lem6019644 _122572 _122573 op) (@lem6019643 _122572 _122573 op)). Qed.
Lemma lem6019646 {_122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : @monoidal _122573 op.
Proof. exact (h1). Qed.
Lemma lem6019647 {_122572 _122573 : Type'} (op : type1400 _122573) (h1 : @monoidal _122573 op) : term16 _122572 _122573 op.
Proof. exact (@lem6019645 _122572 _122573 op (@lem6019646 _122573 op h1)). Qed.
Lemma lem6019648 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term249 _122572 _122573 op f.
Proof. exact (@lem6019647 _122572 _122573 op h1 f). Qed.
Lemma lem6019649 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) : (term249 _122572 _122573 op f) = (term12 _122572 _122573 op f).
Proof. exact (eq_refl (term249 _122572 _122573 op f)). Qed.
Lemma lem6019650 {_122572 _122573 : Type'} (f : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term12 _122572 _122573 op f.
Proof. exact (EQ_MP (@lem6019649 _122572 _122573 op f) (@lem6019648 _122572 _122573 f op h1)). Qed.
Lemma lem6019651 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term250 _122572 _122573 op f g.
Proof. exact (@lem6019650 _122572 _122573 f op h1 g). Qed.
Lemma lem6019652 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term250 _122572 _122573 op f g) = (term8 _122572 _122573 op f g).
Proof. exact (eq_refl (term250 _122572 _122573 op f g)). Qed.
Lemma lem6019653 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term8 _122572 _122573 op f g.
Proof. exact (EQ_MP (@lem6019652 _122572 _122573 op f g) (@lem6019651 _122572 _122573 f g op h1)). Qed.
Lemma lem6019654 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term251 _122572 _122573 op f g s.
Proof. exact (@lem6019653 _122572 _122573 f g op h1 s). Qed.
Lemma lem6019655 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term251 _122572 _122573 op f g s) = (term4 _122572 _122573 s op f g).
Proof. exact (eq_refl (term251 _122572 _122573 op f g s)). Qed.
Lemma lem6019656 {_122572 _122573 : Type'} (s : _122572 -> Prop) (f : _122572 -> _122573) (g : _122572 -> _122573) (op : type1400 _122573) (h1 : @monoidal _122573 op) : term4 _122572 _122573 s op f g.
Proof. exact (EQ_MP (@lem6019655 _122572 _122573 s op f g) (@lem6019654 _122572 _122573 f g s op h1)). Qed.
Lemma lem6019657 {_122572 : Type'} (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : @FINITE _122572 s.
Proof. exact (h1). Qed.
Lemma lem6019658 {_122572 _122573 : Type'} (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (op : type1400 _122573) (h1 : @FINITE _122572 s) (h2 : @monoidal _122573 op) : (term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g).
Proof. exact (@lem6019656 _122572 _122573 s f g op h2 (@lem6019657 _122572 s h1)). Qed.
Lemma lem6019659 {_122572 _122573 : Type'} (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) (s : _122572 -> Prop) (h1 : @FINITE _122572 s) : term252 _122572 _122573 s op f g.
Proof. exact (fun h0 : @monoidal _122573 op => @lem6019658 _122572 _122573 f g s op h1 h0). Qed.
Lemma lem6019660 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : term253 _122572 _122573 s op f g.
Proof. exact (fun h0 : @FINITE _122572 s => @lem6019659 _122572 _122573 op f g s h0). Qed.
Lemma lem6019662 (p : Prop) (q : Prop) (r : Prop) : (term37 p q r) = (term36 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6019667 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : (term253 _122572 _122573 s op f g) = (term254 _122572 _122573 s op f g).
Proof. exact (@lem6019662 (@FINITE _122572 s) (@monoidal _122573 op) ((term1 _122572 _122573 f op s g) = (term0 _122572 _122573 s op f g))). Qed.
Lemma lem6019669 {A B : Type'} (op : type1400 B) : term255 A B op.
Proof. exact (@lem5804540 A B op). Qed.
Lemma lem6019670 {A B : Type'} (op : type1400 B) : (term255 A B op) = (term256 A B op).
Proof. exact (eq_refl (term255 A B op)). Qed.
Lemma lem6019671 {A B : Type'} (op : type1400 B) : term256 A B op.
Proof. exact (EQ_MP (@lem6019670 A B op) (@lem6019669 A B op)). Qed.
Lemma lem6019672 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6019673 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term257 A B op.
Proof. exact (@lem6019671 A B op (@lem6019672 B op h1)). Qed.
Lemma lem6019674 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term258 A B op f.
Proof. exact (@lem6019673 A B op h1 f). Qed.
Lemma lem6019675 {A B : Type'} (f : A -> B) (op : type1400 B) : (term258 A B op f) = (term259 A B f op).
Proof. exact (eq_refl (term258 A B op f)). Qed.
Lemma lem6019676 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term259 A B f op.
Proof. exact (EQ_MP (@lem6019675 A B f op) (@lem6019674 A B f op h1)). Qed.
Lemma lem6019677 {A B : Type'} (f : A -> B) (s : A -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term260 A B f op s.
Proof. exact (@lem6019676 A B f op h1 s). Qed.
Lemma lem6019678 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term260 A B f op s) = (term261 A B s f op).
Proof. exact (eq_refl (term260 A B f op s)). Qed.
Lemma lem6019679 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term261 A B s f op.
Proof. exact (EQ_MP (@lem6019678 A B s f op) (@lem6019677 A B f s op h1)). Qed.
Lemma lem6019680 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term262 A B s f op) : term262 A B s f op.
Proof. exact (h1). Qed.
Lemma lem6019681 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term262 A B s f op) (h2 : @monoidal B op) : (@iterate B A op s f) = (@neutral B op).
Proof. exact (@lem6019679 A B s f op h2 (@lem6019680 A B s f op h1)). Qed.
Lemma lem6019682 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : term262 A B s f op) : term263 A B s f op.
Proof. exact (fun h0 : @monoidal B op => @lem6019681 A B s f op h1 h0). Qed.
Lemma lem6019683 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term264 A B s f op.
Proof. exact (fun h0 : term262 A B s f op => @lem6019682 A B s f op h0). Qed.
Lemma lem6019685 (p : Prop) (q : Prop) (r : Prop) : (term37 p q r) = (term36 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem6019690 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term264 A B s f op) = (term265 A B s f op).
Proof. exact (@lem6019685 (term262 A B s f op) (@monoidal B op) ((@iterate B A op s f) = (@neutral B op))). Qed.
Lemma lem6019692 {C : Type'} (op : type1400 C) : (@monoidal C op) = ((@monoidal C op) = True).
Proof. exact (@lem7 (@monoidal C op)). Qed.
Lemma lem6019717 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6019718 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6019717 p q p' q'). Qed.
Lemma lem6019719 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6019718 p q p'). Qed.
Lemma lem6019720 {B C : Type'} (t : B -> Prop) (op : type1400 C) : term266 B C t op.
Proof. exact (@lem6019719 (@FINITE B t) ((@neutral C op) = (term138 B C t op))). Qed.
Lemma lem6019721 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) : term267 B C t op p'.
Proof. exact (@lem6019720 B C t op p'). Qed.
Lemma lem6019722 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) : (term267 B C t op p') = (term268 B C t op p').
Proof. exact (eq_refl (term267 B C t op p')). Qed.
Lemma lem6019723 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) : term268 B C t op p'.
Proof. exact (EQ_MP (@lem6019722 B C t op p') (@lem6019721 B C t op p')). Qed.
Lemma lem6019724 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) (q' : Prop) : term269 B C t op p' q'.
Proof. exact (@lem6019723 B C t op p' q'). Qed.
Lemma lem6019725 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) (q' : Prop) : (term269 B C t op p' q') = (term270 B C t op p' q').
Proof. exact (eq_refl (term269 B C t op p' q')). Qed.
Lemma lem6019726 {B C : Type'} (t : B -> Prop) (op : type1400 C) (p' : Prop) (q' : Prop) : term270 B C t op p' q'.
Proof. exact (EQ_MP (@lem6019725 B C t op p' q') (@lem6019724 B C t op p' q')). Qed.
Lemma lem6019733 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6019734 {B C : Type'} (op : type1400 C) (t : B -> Prop) (q' : Prop) : term271 B C op t q'.
Proof. exact (@lem6019726 B C t op (@FINITE B t) q'). Qed.
Lemma lem6019735 {B C : Type'} (op : type1400 C) (t : B -> Prop) (q' : Prop) : term272 B C op t q'.
Proof. exact (@lem6019734 B C op t q' (@lem6019733 B t)). Qed.
Lemma lem6019754 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term265 A B s f op.
Proof. exact (EQ_MP (@lem6019690 A B s f op) (@lem6019683 A B s f op)). Qed.
Lemma lem6019755 {B C : Type'} (s : B -> Prop) (f : B -> C) (op : type1400 C) : term265 B C s f op.
Proof. exact (@lem6019754 B C s f op). Qed.
Lemma lem6019756 {B C : Type'} (t : B -> Prop) (op : type1400 C) : term273 B C t op.
Proof. exact (@lem6019755 B C t (term137 B C op) op). Qed.
Lemma lem6019780 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6019781 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6019780 p q p' q'). Qed.
Lemma lem6019782 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6019781 p q p'). Qed.
Lemma lem6019783 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) : term274 B C t x op.
Proof. exact (@lem6019782 (@IN B x t) ((term275 B C op x) = (@neutral C op))). Qed.
Lemma lem6019784 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) : term276 B C t x op p'.
Proof. exact (@lem6019783 B C t x op p'). Qed.
Lemma lem6019785 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) : (term276 B C t x op p') = (term277 B C t x op p').
Proof. exact (eq_refl (term276 B C t x op p')). Qed.
Lemma lem6019786 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) : term277 B C t x op p'.
Proof. exact (EQ_MP (@lem6019785 B C t x op p') (@lem6019784 B C t x op p')). Qed.
Lemma lem6019787 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) (q' : Prop) : term278 B C t x op p' q'.
Proof. exact (@lem6019786 B C t x op p' q'). Qed.
Lemma lem6019788 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) (q' : Prop) : (term278 B C t x op p' q') = (term279 B C t x op p' q').
Proof. exact (eq_refl (term278 B C t x op p' q')). Qed.
Lemma lem6019789 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) (p' : Prop) (q' : Prop) : term279 B C t x op p' q'.
Proof. exact (EQ_MP (@lem6019788 B C t x op p' q') (@lem6019787 B C t x op p' q')). Qed.
Lemma lem6019800 {B : Type'} (x : B) (t : B -> Prop) : (@IN B x t) = (@IN B x t).
Proof. exact (eq_refl (@IN B x t)). Qed.
Lemma lem6019801 {B C : Type'} (op : type1400 C) (x : B) (t : B -> Prop) (q' : Prop) : term280 B C op x t q'.
Proof. exact (@lem6019789 B C t x op (@IN B x t) q'). Qed.
Lemma lem6019802 {B C : Type'} (op : type1400 C) (x : B) (t : B -> Prop) (q' : Prop) : term281 B C op x t q'.
Proof. exact (@lem6019801 B C op x t q' (@lem6019800 B x t)). Qed.
Lemma lem6019815 {A B : Type'} (f : A -> B) (y : A) : (term187 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6019816 {B C : Type'} (f : B -> C) (y : B) : (term187 B C f y) = (f y).
Proof. exact (@lem6019815 B C f y). Qed.
Lemma lem6019817 {B C : Type'} (op : type1400 C) (x : B) : (term282 B C op x) = (term275 B C op x).
Proof. exact (@lem6019816 B C (term137 B C op) x). Qed.
Lemma lem6019818 {B C : Type'} (j : B) (op : type1400 C) : (term275 B C op j) = (@neutral C op).
Proof. exact (eq_refl (term275 B C op j)). Qed.
Lemma lem6019819 {B C : Type'} (op : type1400 C) : (term283 B C op) = (term137 B C op).
Proof. exact (fun_ext (fun j : B => @lem6019818 B C j op)). Qed.
Lemma lem6019820 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6019821 {B C : Type'} (op : type1400 C) (x : B) : (term282 B C op x) = (term275 B C op x).
Proof. exact (MK_COMB (@lem6019819 B C op) (@lem6019820 B x)). Qed.
Lemma lem6019822 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6019823 {B C : Type'} (op : type1400 C) (x : B) : (term284 B C op x) = (term285 B C op x).
Proof. exact (MK_COMB (@lem6019822 C) (@lem6019821 B C op x)). Qed.
Lemma lem6019824 {B C : Type'} (x : B) (op : type1400 C) : (term275 B C op x) = (@neutral C op).
Proof. exact (eq_refl (term275 B C op x)). Qed.
Lemma lem6019825 {B C : Type'} (x : B) (op : type1400 C) : ((term282 B C op x) = (term275 B C op x)) = ((term275 B C op x) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6019823 B C op x) (@lem6019824 B C x op)). Qed.
Lemma lem6019826 {B C : Type'} (x : B) (op : type1400 C) : (term275 B C op x) = (@neutral C op).
Proof. exact (EQ_MP (@lem6019825 B C x op) (@lem6019817 B C op x)). Qed.
Lemma lem6019833 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6019834 {B C : Type'} (x : B) (op : type1400 C) : (term285 B C op x) = (term132 C op).
Proof. exact (MK_COMB (@lem6019833 C) (@lem6019826 B C x op)). Qed.
Lemma lem6019851 {C : Type'} (op : type1400 C) : (@neutral C op) = (@neutral C op).
Proof. exact (eq_refl (@neutral C op)). Qed.
Lemma lem6019852 {B C : Type'} (x : B) (op : type1400 C) : ((term275 B C op x) = (@neutral C op)) = ((@neutral C op) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6019834 B C x op) (@lem6019851 C op)). Qed.
Lemma lem6019854 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6019855 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6019854 C x). Qed.
Lemma lem6019856 {C : Type'} (op : type1400 C) : ((@neutral C op) = (@neutral C op)) = True.
Proof. exact (@lem6019855 C (@neutral C op)). Qed.
Lemma lem6019859 {B C : Type'} (x : B) (op : type1400 C) : ((term275 B C op x) = (@neutral C op)) = True.
Proof. exact (TRANS (@lem6019852 B C x op) (@lem6019856 C op)). Qed.
Lemma lem6019860 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) : term286 B C t x op.
Proof. exact (fun h0 : @IN B x t => @lem6019859 B C x op). Qed.
Lemma lem6019861 {B C : Type'} (op : type1400 C) (x : B) (t : B -> Prop) : term287 B C op x t.
Proof. exact (@lem6019802 B C op x t True). Qed.
Lemma lem6019862 {B C : Type'} (op : type1400 C) (x : B) (t : B -> Prop) : (term288 B C t x op) = (term289 B x t).
Proof. exact (@lem6019861 B C op x t (@lem6019860 B C t x op)). Qed.
Lemma lem6019864 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6019865 {B : Type'} (x : B) (t : B -> Prop) : (term289 B x t) = True.
Proof. exact (@lem6019864 (@IN B x t)). Qed.
Lemma lem6019868 {B C : Type'} (t : B -> Prop) (x : B) (op : type1400 C) : (term288 B C t x op) = True.
Proof. exact (TRANS (@lem6019862 B C op x t) (@lem6019865 B x t)). Qed.
Lemma lem6019869 {B C : Type'} (t : B -> Prop) (op : type1400 C) : (term290 B C t op) = (term291 B).
Proof. exact (fun_ext (fun x : B => @lem6019868 B C t x op)). Qed.
Lemma lem6019874 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem6019875 {B C : Type'} (t : B -> Prop) (op : type1400 C) : (term292 B C t op) = (term293 B).
Proof. exact (MK_COMB (@lem6019874 B) (@lem6019869 B C t op)). Qed.
Lemma lem6019877 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6019878 {B : Type'} (t : Prop) : (term294 B t) = t.
Proof. exact (@lem6019877 B t). Qed.
Lemma lem6019879 {B : Type'} : (term293 B) = True.
Proof. exact (@lem6019878 B True). Qed.
Lemma lem6019882 {B C : Type'} (t : B -> Prop) (op : type1400 C) : (term292 B C t op) = True.
Proof. exact (TRANS (@lem6019875 B C t op) (@lem6019879 B)). Qed.
Lemma lem6019883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6019884 {B C : Type'} (t : B -> Prop) (op : type1400 C) : (term295 B C t op) = (and True).
Proof. exact (MK_COMB (@lem6019883) (@lem6019882 B C t op)). Qed.
Lemma lem6019892 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6019692 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6019895 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term296 B C t op) = (True /\ True).
Proof. exact (MK_COMB (@lem6019884 B C t op) (@lem6019892 C op h1)). Qed.
Lemma lem6019897 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6019898 : (True /\ True) = True.
Proof. exact (@lem6019897 True). Qed.
Lemma lem6019901 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term296 B C t op) = True.
Proof. exact (TRANS (@lem6019895 B C t op h1) (@lem6019898)). Qed.
Lemma lem6019902 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : True = (term296 B C t op).
Proof. exact (SYM (@lem6019901 B C t op h1)). Qed.
Lemma lem6019903 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term296 B C t op.
Proof. exact (EQ_MP (@lem6019902 B C t op h1) (@lem0)). Qed.
Lemma lem6019904 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term138 B C t op) = (@neutral C op).
Proof. exact (@lem6019756 B C t op (@lem6019903 B C t op h1)). Qed.
Lemma lem6019911 {C : Type'} (op : type1400 C) : (term132 C op) = (term132 C op).
Proof. exact (eq_refl (term132 C op)). Qed.
Lemma lem6019912 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : ((@neutral C op) = (term138 B C t op)) = ((@neutral C op) = (@neutral C op)).
Proof. exact (MK_COMB (@lem6019911 C op) (@lem6019904 B C t op h1)). Qed.
Lemma lem6019914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6019915 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6019914 C x). Qed.
Lemma lem6019916 {C : Type'} (op : type1400 C) : ((@neutral C op) = (@neutral C op)) = True.
Proof. exact (@lem6019915 C (@neutral C op)). Qed.
Lemma lem6019919 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : ((@neutral C op) = (term138 B C t op)) = True.
Proof. exact (TRANS (@lem6019912 B C t op h1) (@lem6019916 C op)). Qed.
Lemma lem6019920 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : term297 B C t op.
Proof. exact (fun h0 : @FINITE B t => @lem6019919 B C t op h1). Qed.
Lemma lem6019921 {B C : Type'} (op : type1400 C) (t : B -> Prop) : term298 B C op t.
Proof. exact (@lem6019735 B C op t True). Qed.
Lemma lem6019922 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term142 B C t op) = (term299 B t).
Proof. exact (@lem6019921 B C op t (@lem6019920 B C t op h1)). Qed.
Lemma lem6019924 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6019925 {B : Type'} (t : B -> Prop) : (term299 B t) = True.
Proof. exact (@lem6019924 (@FINITE B t)). Qed.
Lemma lem6019928 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term142 B C t op) = True.
Proof. exact (TRANS (@lem6019922 B C t op h1) (@lem6019925 B t)). Qed.
Lemma lem6019929 {B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term144 B C op) = (term300 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6019928 B C t op h1)). Qed.
Lemma lem6019934 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6019935 {B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term145 B C op) = (term301 B).
Proof. exact (MK_COMB (@lem6019934 B) (@lem6019929 B C op h1)). Qed.
Lemma lem6019937 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6019938 {B : Type'} (t : Prop) : (term302 B t) = t.
Proof. exact (@lem6019937 (B -> Prop) t). Qed.
Lemma lem6019939 {B : Type'} : (term301 B) = True.
Proof. exact (@lem6019938 B True). Qed.
Lemma lem6019942 {B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term145 B C op) = True.
Proof. exact (TRANS (@lem6019935 B C op h1) (@lem6019939 B)). Qed.
Lemma lem6019943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6019944 {B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (term146 B C op) = (and True).
Proof. exact (MK_COMB (@lem6019943) (@lem6019942 B C op h1)). Qed.
Lemma lem6019976 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6019977 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6019976 p q p' q'). Qed.
Lemma lem6019978 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6019977 p q p'). Qed.
Lemma lem6019979 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : term303 A B C x op s f.
Proof. exact (@lem6019978 (term76 A B C op f x s) (term239 A B C x op s f)). Qed.
Lemma lem6019980 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term304 A B C x op s f p'.
Proof. exact (@lem6019979 A B C x op s f p'). Qed.
Lemma lem6019981 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : (term304 A B C x op s f p') = (term305 A B C x op s f p').
Proof. exact (eq_refl (term304 A B C x op s f p')). Qed.
Lemma lem6019982 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term305 A B C x op s f p'.
Proof. exact (EQ_MP (@lem6019981 A B C x op s f p') (@lem6019980 A B C x op s f p')). Qed.
Lemma lem6019983 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term306 A B C x op s f p' q'.
Proof. exact (@lem6019982 A B C x op s f p' q'). Qed.
Lemma lem6019984 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term306 A B C x op s f p' q') = (term307 A B C x op s f p' q').
Proof. exact (eq_refl (term306 A B C x op s f p' q')). Qed.
Lemma lem6019985 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term307 A B C x op s f p' q'.
Proof. exact (EQ_MP (@lem6019984 A B C x op s f p' q') (@lem6019983 A B C x op s f p' q')). Qed.
Lemma lem6048909 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : (term76 A B C op f x s) = (term76 A B C op f x s).
Proof. exact (eq_refl (term76 A B C op f x s)). Qed.
Lemma lem6048910 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (q' : Prop) : term308 A B C op f x s q'.
Proof. exact (@lem6019985 A B C x op s f (term76 A B C op f x s) q'). Qed.
Lemma lem6048911 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) (q' : Prop) : term309 A B C op f x s q'.
Proof. exact (@lem6048910 A B C op f x s q' (@lem6048909 A B C op f x s)). Qed.
Lemma lem6048946 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term116 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6048947 (p : Prop) (q : Prop) (p' : Prop) : term117 p q p'.
Proof. exact (fun q' : Prop => @lem6048946 p q p' q'). Qed.
Lemma lem6048948 (p : Prop) (q : Prop) : term118 p q.
Proof. exact (fun p' : Prop => @lem6048947 p q p'). Qed.
Lemma lem6048949 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : term310 A B C t x op s f.
Proof. exact (@lem6048948 (@FINITE B t) ((term196 A B C x t op s f) = (term232 A B C t x op s f))). Qed.
Lemma lem6048950 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term311 A B C t x op s f p'.
Proof. exact (@lem6048949 A B C t x op s f p'). Qed.
Lemma lem6048951 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : (term311 A B C t x op s f p') = (term312 A B C t x op s f p').
Proof. exact (eq_refl (term311 A B C t x op s f p')). Qed.
Lemma lem6048952 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) : term312 A B C t x op s f p'.
Proof. exact (EQ_MP (@lem6048951 A B C t x op s f p') (@lem6048950 A B C t x op s f p')). Qed.
Lemma lem6048953 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term313 A B C t x op s f p' q'.
Proof. exact (@lem6048952 A B C t x op s f p' q'). Qed.
Lemma lem6048954 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : (term313 A B C t x op s f p' q') = (term314 A B C t x op s f p' q').
Proof. exact (eq_refl (term313 A B C t x op s f p' q')). Qed.
Lemma lem6048955 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (p' : Prop) (q' : Prop) : term314 A B C t x op s f p' q'.
Proof. exact (EQ_MP (@lem6048954 A B C t x op s f p' q') (@lem6048953 A B C t x op s f p' q')). Qed.
Lemma lem6048962 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem6048963 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term315 A B C x op s f t q'.
Proof. exact (@lem6048955 A B C t x op s f (@FINITE B t) q'). Qed.
Lemma lem6048964 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (q' : Prop) : term316 A B C x op s f t q'.
Proof. exact (@lem6048963 A B C x op s f t q' (@lem6048962 B t)). Qed.
Lemma lem6048965 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem6048966 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem6048977 {_122572 _122573 : Type'} (s : _122572 -> Prop) (op : type1400 _122573) (f : _122572 -> _122573) (g : _122572 -> _122573) : term254 _122572 _122573 s op f g.
Proof. exact (EQ_MP (@lem6019667 _122572 _122573 s op f g) (@lem6019660 _122572 _122573 s op f g)). Qed.
Lemma lem6048978 {B C : Type'} (s : B -> Prop) (op : type1400 C) (f : B -> C) (g : B -> C) : term254 B C s op f g.
Proof. exact (@lem6048977 B C s op f g). Qed.
Lemma lem6048979 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : term317 A B C t x op s f.
Proof. exact (@lem6048978 B C t op (f x) (term318 A B C op s f)). Qed.
Lemma lem6048989 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem6048966 B t) (@lem6048965 B t h1)). Qed.
Lemma lem6048992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6048993 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (term167 B t) = (and True).
Proof. exact (MK_COMB (@lem6048992) (@lem6048989 B t h1)). Qed.
Lemma lem6049001 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : (@monoidal C op) = True.
Proof. exact (EQ_MP (@lem6019692 C op) (@lem6017809 C op h1)). Qed.
Lemma lem6049004 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : (term168 B C t op) = (True /\ True).
Proof. exact (MK_COMB (@lem6048993 B t h1) (@lem6049001 C op h2)). Qed.
Lemma lem6049006 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6049007 : (True /\ True) = True.
Proof. exact (@lem6049006 True). Qed.
Lemma lem6049010 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : (term168 B C t op) = True.
Proof. exact (TRANS (@lem6049004 B C t op h1 h2) (@lem6049007)). Qed.
Lemma lem6049011 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : True = (term168 B C t op).
Proof. exact (SYM (@lem6049010 B C t op h1 h2)). Qed.
Lemma lem6049012 {B C : Type'} (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : term168 B C t op.
Proof. exact (EQ_MP (@lem6049011 B C t op h1 h2) (@lem0)). Qed.
Lemma lem6049013 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : (term196 A B C x t op s f) = (term319 A B C t x op s f).
Proof. exact (@lem6048979 A B C t x op s f (@lem6049012 B C t op h1 h2)). Qed.
Lemma lem6064400 {A B : Type'} (f : A -> B) (y : A) : (term187 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6064401 {B C : Type'} (f : B -> C) (y : B) : (term187 B C f y) = (f y).
Proof. exact (@lem6064400 B C f y). Qed.
Lemma lem6064402 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : (term320 A B C op s f x) = (term321 A B C op s f x).
Proof. exact (@lem6064401 B C (term318 A B C op s f) x). Qed.
Lemma lem6064403 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (j : B) : (term321 A B C op s f j) = (term206 A B C op s f j).
Proof. exact (eq_refl (term321 A B C op s f j)). Qed.
Lemma lem6064404 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term322 A B C op s f) = (term318 A B C op s f).
Proof. exact (fun_ext (fun j : B => @lem6064403 A B C op s f j)). Qed.
Lemma lem6064405 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6064406 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : (term320 A B C op s f x) = (term321 A B C op s f x).
Proof. exact (MK_COMB (@lem6064404 A B C op s f) (@lem6064405 B x)). Qed.
Lemma lem6064407 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6064408 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : (term323 A B C op s f x) = (term324 A B C op s f x).
Proof. exact (MK_COMB (@lem6064407 C) (@lem6064406 A B C op s f x)). Qed.
Lemma lem6064409 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : (term321 A B C op s f x) = (term206 A B C op s f x).
Proof. exact (eq_refl (term321 A B C op s f x)). Qed.
Lemma lem6064410 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : ((term320 A B C op s f x) = (term321 A B C op s f x)) = ((term321 A B C op s f x) = (term206 A B C op s f x)).
Proof. exact (MK_COMB (@lem6064408 A B C op s f x) (@lem6064409 A B C op s f x)). Qed.
Lemma lem6064411 {A B C : Type'} (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x : B) : (term321 A B C op s f x) = (term206 A B C op s f x).
Proof. exact (EQ_MP (@lem6064410 A B C op s f x) (@lem6064402 A B C op s f x)). Qed.
Lemma lem6065453 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (x' : B) : (term225 A B C op f x x') = (term225 A B C op f x x').
Proof. exact (eq_refl (term225 A B C op f x x')). Qed.
Lemma lem6065454 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (x' : B) : (term325 A B C x op s f x') = (term226 A B C x op s f x').
Proof. exact (MK_COMB (@lem6065453 A B C op f x x') (@lem6064411 A B C op s f x')). Qed.
Lemma lem6066512 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term326 A B C x op s f) = (term231 A B C x op s f).
Proof. exact (fun_ext (fun x' : B => @lem6065454 A B C x op s f x')). Qed.
Lemma lem6067572 {B C : Type'} (op : type1400 C) (t : B -> Prop) : (@iterate C B op t) = (@iterate C B op t).
Proof. exact (eq_refl (@iterate C B op t)). Qed.
Lemma lem6067573 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term319 A B C t x op s f) = (term232 A B C t x op s f).
Proof. exact (MK_COMB (@lem6067572 B C op t) (@lem6066512 A B C x op s f)). Qed.
Lemma lem6082927 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : (term196 A B C x t op s f) = (term232 A B C t x op s f).
Proof. exact (TRANS (@lem6049013 A B C x s f t op h1 h2) (@lem6067573 A B C t x op s f)). Qed.
Lemma lem6082928 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem6082929 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : (term201 A B C x t op s f) = (term327 A B C t x op s f).
Proof. exact (MK_COMB (@lem6082928 C) (@lem6082927 A B C x s f t op h1 h2)). Qed.
Lemma lem6113640 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term232 A B C t x op s f) = (term232 A B C t x op s f).
Proof. exact (eq_refl (term232 A B C t x op s f)). Qed.
Lemma lem6113641 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : ((term196 A B C x t op s f) = (term232 A B C t x op s f)) = ((term232 A B C t x op s f) = (term232 A B C t x op s f)).
Proof. exact (MK_COMB (@lem6082929 A B C x s f t op h1 h2) (@lem6113640 A B C t x op s f)). Qed.
Lemma lem6113643 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6113644 {C : Type'} (x : C) : (x = x) = True.
Proof. exact (@lem6113643 C x). Qed.
Lemma lem6113645 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True.
Proof. exact (@lem6113644 C (term232 A B C t x op s f)). Qed.
Lemma lem6113648 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term328 A B C t x op s f) = (term328 A B C t x op s f).
Proof. exact (eq_refl (term328 A B C t x op s f)). Qed.
Lemma lem6113649 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term328 A B C t x op s f) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True).
Proof. exact (eq_refl (term328 A B C t x op s f)). Qed.
Lemma lem6113650 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term329 A B C t x op s f) = (term329 A B C t x op s f).
Proof. exact (eq_refl (term329 A B C t x op s f)). Qed.
Lemma lem6113651 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term328 A B C t x op s f) = (term328 A B C t x op s f)) = ((term328 A B C t x op s f) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True)).
Proof. exact (MK_COMB (@lem6113650 A B C t x op s f) (@lem6113649 A B C t x op s f)). Qed.
Lemma lem6113652 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term328 A B C t x op s f) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True).
Proof. exact (eq_refl (term328 A B C t x op s f)). Qed.
Lemma lem6113653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6113654 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (term329 A B C t x op s f) = (term330 A B C t x op s f).
Proof. exact (MK_COMB (@lem6113653) (@lem6113652 A B C t x op s f)). Qed.
Lemma lem6113655 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True).
Proof. exact (eq_refl (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True)). Qed.
Lemma lem6113656 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term328 A B C t x op s f) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True)) = ((((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True)).
Proof. exact (MK_COMB (@lem6113654 A B C t x op s f) (@lem6113655 A B C t x op s f)). Qed.
Lemma lem6113657 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term328 A B C t x op s f) = (term328 A B C t x op s f)) = ((((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True)).
Proof. exact (TRANS (@lem6113651 A B C t x op s f) (@lem6113656 A B C t x op s f)). Qed.
Lemma lem6113658 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True) = (((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True).
Proof. exact (EQ_MP (@lem6113657 A B C t x op s f) (@lem6113648 A B C t x op s f)). Qed.
Lemma lem6113659 {A B C : Type'} (t : B -> Prop) (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) : ((term232 A B C t x op s f) = (term232 A B C t x op s f)) = True.
Proof. exact (EQ_MP (@lem6113658 A B C t x op s f) (@lem6113645 A B C t x op s f)). Qed.
Lemma lem6113662 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @FINITE B t) (h2 : @monoidal C op) : ((term196 A B C x t op s f) = (term232 A B C t x op s f)) = True.
Proof. exact (TRANS (@lem6113641 A B C x s f t op h1 h2) (@lem6113659 A B C t x op s f)). Qed.
Lemma lem6113663 {A B C : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term331 A B C t x op s f.
Proof. exact (fun h0 : @FINITE B t => @lem6113662 A B C x s f t op h0 h1). Qed.
Lemma lem6113664 {A B C : Type'} (x : A) (op : type1400 C) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) : term332 A B C x op s f t.
Proof. exact (@lem6048964 A B C x op s f t True). Qed.
Lemma lem6113665 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (t : B -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term236 A B C t x op s f) = (term299 B t).
Proof. exact (@lem6113664 A B C x op s f t (@lem6113663 A B C t x s f op h1)). Qed.
Lemma lem6113667 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6113668 {B : Type'} (t : B -> Prop) : (term299 B t) = True.
Proof. exact (@lem6113667 (@FINITE B t)). Qed.
Lemma lem6113671 {A B C : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term236 A B C t x op s f) = True.
Proof. exact (TRANS (@lem6113665 A B C x s f t op h1) (@lem6113668 B t)). Qed.
Lemma lem6113672 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term238 A B C x op s f) = (term300 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem6113671 A B C t x s f op h1)). Qed.
Lemma lem6113677 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem6113678 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term239 A B C x op s f) = (term301 B).
Proof. exact (MK_COMB (@lem6113677 B) (@lem6113672 A B C x s f op h1)). Qed.
Lemma lem6113680 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6113681 {B : Type'} (t : Prop) : (term302 B t) = t.
Proof. exact (@lem6113680 (B -> Prop) t). Qed.
Lemma lem6113682 {B : Type'} : (term301 B) = True.
Proof. exact (@lem6113681 B True). Qed.
Lemma lem6113685 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term239 A B C x op s f) = True.
Proof. exact (TRANS (@lem6113678 A B C x s f op h1) (@lem6113682 B)). Qed.
Lemma lem6113686 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term333 A B C x op s f.
Proof. exact (fun h0 : term76 A B C op f x s => @lem6113685 A B C x s f op h1). Qed.
Lemma lem6113687 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : term334 A B C op f x s.
Proof. exact (@lem6048911 A B C op f x s True). Qed.
Lemma lem6113688 {A B C : Type'} (f : type1412 A B C) (x : A) (s : A -> Prop) (op : type1400 C) (h1 : @monoidal C op) : (term242 A B C x op s f) = (term335 A B C op f x s).
Proof. exact (@lem6113687 A B C op f x s (@lem6113686 A B C x s f op h1)). Qed.
Lemma lem6113690 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6113691 {A B C : Type'} (op : type1400 C) (f : type1412 A B C) (x : A) (s : A -> Prop) : (term335 A B C op f x s) = True.
Proof. exact (@lem6113690 (term76 A B C op f x s)). Qed.
Lemma lem6113694 {A B C : Type'} (x : A) (s : A -> Prop) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term242 A B C x op s f) = True.
Proof. exact (TRANS (@lem6113688 A B C f x s op h1) (@lem6113691 A B C op f x s)). Qed.
Lemma lem6113695 {A B C : Type'} (x : A) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term243 A B C x op f) = (term300 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6113694 A B C x s f op h1)). Qed.
Lemma lem6113700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6113701 {A B C : Type'} (x : A) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term244 A B C x op f) = (term301 A).
Proof. exact (MK_COMB (@lem6113700 A) (@lem6113695 A B C x f op h1)). Qed.
Lemma lem6113703 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6113704 {A : Type'} (t : Prop) : (term302 A t) = t.
Proof. exact (@lem6113703 (A -> Prop) t). Qed.
Lemma lem6113705 {A : Type'} : (term301 A) = True.
Proof. exact (@lem6113704 A True). Qed.
Lemma lem6113708 {A B C : Type'} (x : A) (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term244 A B C x op f) = True.
Proof. exact (TRANS (@lem6113701 A B C x f op h1) (@lem6113705 A)). Qed.
Lemma lem6113709 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term245 A B C op f) = (term291 A).
Proof. exact (fun_ext (fun x : A => @lem6113708 A B C x f op h1)). Qed.
Lemma lem6113714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6113715 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term246 A B C op f) = (term293 A).
Proof. exact (MK_COMB (@lem6113714 A) (@lem6113709 A B C f op h1)). Qed.
Lemma lem6113717 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6113718 {A : Type'} (t : Prop) : (term294 A t) = t.
Proof. exact (@lem6113717 A t). Qed.
Lemma lem6113719 {A : Type'} : (term293 A) = True.
Proof. exact (@lem6113718 A True). Qed.
Lemma lem6113722 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term246 A B C op f) = True.
Proof. exact (TRANS (@lem6113715 A B C f op h1) (@lem6113719 A)). Qed.
Lemma lem6113723 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term247 A B C op f) = (True /\ True).
Proof. exact (MK_COMB (@lem6019944 B C op h1) (@lem6113722 A B C f op h1)). Qed.
Lemma lem6113725 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6113726 : (True /\ True) = True.
Proof. exact (@lem6113725 True). Qed.
Lemma lem6113729 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : (term247 A B C op f) = True.
Proof. exact (TRANS (@lem6113723 A B C f op h1) (@lem6113726)). Qed.
Lemma lem6113730 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : True = (term247 A B C op f).
Proof. exact (SYM (@lem6113729 A B C f op h1)). Qed.
Lemma lem6113731 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term247 A B C op f.
Proof. exact (EQ_MP (@lem6113730 A B C f op h1) (@lem0)). Qed.
Lemma lem6113732 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term92 A B C op f.
Proof. exact (EQ_MP (@lem6019642 A B C f op h1) (@lem6113731 A B C f op h1)). Qed.
Lemma lem6113733 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term64 A B C op f.
Proof. exact (@lem6017961 A B C op f (@lem6113732 A B C f op h1)). Qed.
Lemma lem6113734 {A B C : Type'} (f : type1412 A B C) (op : type1400 C) (h1 : @monoidal C op) : term63 A B C op f.
Proof. exact (EQ_MP (@lem6017928 A B C op f) (@lem6113733 A B C f op h1)). Qed.
Lemma lem6113739 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term336 A B C op.
Proof. exact (fun f : type1412 A B C => @lem6113734 A B C f op h1). Qed.
Lemma lem6113740 {A B C : Type'} (op : type1400 C) : term337 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem6113739 A B C op h0). Qed.
Lemma lem6113745 {A B C : Type'} : term338 A B C.
Proof. exact (fun op : type1400 C => @lem6113740 A B C op). Qed.
