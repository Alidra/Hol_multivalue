Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTER_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import INTER_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm69_spec.
Lemma lem3606773 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3606774 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3606775 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3606774 t1) (@lem3606773 t1)). Qed.
Lemma lem3606776 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3606775 t1 t2). Qed.
Lemma lem3606777 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3606778 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3606777 t1 t2) (@lem3606776 t1 t2)). Qed.
Lemma lem3606779 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3606778 t1 t2 t3). Qed.
Lemma lem3606780 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3606781 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3606780 t1 t2 t3) (@lem3606779 t1 t2 t3)). Qed.
Lemma lem3606782 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3606781 t1 t2 t3)). Qed.
Lemma lem3606784 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3606785 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (@lem3606784 (term8 A)). Qed.
Lemma lem3606786 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3606785 A)). Qed.
Lemma lem3606787 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3606788 {A : Type'} : term11 A.
Proof. exact (@lem3256723 A). Qed.
Lemma lem3606789 {A : Type'} : term12 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3606793 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3606794 {A : Type'} : term14 A.
Proof. exact (fun h0 : term13 A => @lem3606793 A h0). Qed.
Lemma lem3606795 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3606796 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3606797 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3606795 A h2 (@lem3606796 A h1)). Qed.
Lemma lem3606798 {A : Type'} (h1 : term13 A) : term15 A.
Proof. exact (fun h0 : term14 A => @lem3606797 A h1 h0). Qed.
Lemma lem3606799 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (h1). Qed.
Lemma lem3606800 {A : Type'} (h1 : term13 A) (h2 : term14 A) : term13 A.
Proof. exact (@lem3606798 A h1 (@lem3606799 A h2)). Qed.
Lemma lem3606801 {A : Type'} (h1 : term14 A) : term14 A.
Proof. exact (fun h0 : term13 A => @lem3606800 A h0 h1). Qed.
Lemma lem3606802 {A : Type'} : term16 A.
Proof. exact (fun h0 : term14 A => @lem3606801 A h0). Qed.
Lemma lem3606805 {A : Type'} : term14 A.
Proof. exact (@lem3606802 A (@lem3606794 A)). Qed.
Lemma lem3606806 {A : Type'} : term14 A.
Proof. exact (@lem3606805 A). Qed.
Lemma lem3606836 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3606837 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem3606836 (term11 A)). Qed.
Lemma lem3606856 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem3606857 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem3606856 A) (@lem3606837 A)). Qed.
Lemma lem3606860 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem3606867 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (MK_COMB (@lem3606860 A) (@lem3606857 A)). Qed.
Lemma lem3606868 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (eq_refl (term24 A t s)). Qed.
Lemma lem3606869 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606868 A t s)). Qed.
Lemma lem3606870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606871 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3606870 A) (@lem3606869 A s)). Qed.
Lemma lem3606872 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606871 A s)). Qed.
Lemma lem3606873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606874 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3606873 A) (@lem3606872 A)). Qed.
Lemma lem3606875 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (eq_refl (term29 A t s)). Qed.
Lemma lem3606876 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606875 A t s)). Qed.
Lemma lem3606877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606878 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3606877 A) (@lem3606876 A s)). Qed.
Lemma lem3606879 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606878 A s)). Qed.
Lemma lem3606880 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606881 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3606880 A) (@lem3606879 A)). Qed.
Lemma lem3606882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3606883 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3606882) (@lem3606881 A)). Qed.
Lemma lem3606884 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3606883 A) (@lem3606874 A)). Qed.
Lemma lem3606885 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3606886 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem3606885) (@lem3606884 A)). Qed.
Lemma lem3606895 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term35 A t s) = (term35 A t s).
Proof. exact (eq_refl (term35 A t s)). Qed.
Lemma lem3606896 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606895 A t s)). Qed.
Lemma lem3606897 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606898 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3606897 A) (@lem3606896 A s)). Qed.
Lemma lem3606899 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606898 A s)). Qed.
Lemma lem3606900 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606901 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3606900 A) (@lem3606899 A)). Qed.
Lemma lem3606902 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3606903 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3606902) (@lem3606901 A)). Qed.
Lemma lem3606904 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (MK_COMB (@lem3606903 A) (@lem3606886 A)). Qed.
Lemma lem3606913 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (eq_refl (term39 A s t)). Qed.
Lemma lem3606914 {A : Type'} (s : A -> Prop) : (term40 A s) = (term40 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3606913 A s t)). Qed.
Lemma lem3606915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606916 {A : Type'} (s : A -> Prop) : (term41 A s) = (term41 A s).
Proof. exact (MK_COMB (@lem3606915 A) (@lem3606914 A s)). Qed.
Lemma lem3606917 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3606916 A s)). Qed.
Lemma lem3606918 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3606919 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (MK_COMB (@lem3606918 A) (@lem3606917 A)). Qed.
Lemma lem3606920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3606921 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem3606920) (@lem3606919 A)). Qed.
Lemma lem3606922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3606923 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3606922) (@lem3606921 A)). Qed.
Lemma lem3606924 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3606923 A) (@lem3606904 A)). Qed.
Lemma lem3606989 {A : Type'} : (term13 A) = (term23 A).
Proof. exact (TRANS (@lem3606867 A) (@lem3606924 A)). Qed.
Lemma lem3606990 {A : Type'} : (term23 A) = (term13 A).
Proof. exact (SYM (@lem3606989 A)). Qed.
Lemma lem3606991 {A : Type'} (h1 : term10 A) : term10 A.
Proof. exact (h1). Qed.
Lemma lem3606992 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3606993 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (h1). Qed.
Lemma lem3607004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term44 A s t).
Proof. exact (@lem17362 (term45 A s t) (term46 A s t)). Qed.
Lemma lem3607005 {A : Type'} (P : type686 A) : (term47 A P) = (term48 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3607006 {A : Type'} (s : A -> Prop) : (term49 A s) = (term50 A s).
Proof. exact (@lem3607005 A (term40 A s)). Qed.
Lemma lem3607007 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term39 A s t).
Proof. exact (eq_refl (term51 A s t)). Qed.
Lemma lem3607008 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3607009 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3607008) (@lem3607007 A s t)). Qed.
Lemma lem3607010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term52 A s t) = (term44 A s t).
Proof. exact (TRANS (@lem3607009 A s t) (@lem3607004 A s t)). Qed.
Lemma lem3607011 {A : Type'} (s : A -> Prop) : (term53 A s) = (term54 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607010 A s t)). Qed.
Lemma lem3607012 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3607013 {A : Type'} (s : A -> Prop) : (term50 A s) = (term55 A s).
Proof. exact (MK_COMB (@lem3607012 A) (@lem3607011 A s)). Qed.
Lemma lem3607014 {A : Type'} (s : A -> Prop) : (term49 A s) = (term55 A s).
Proof. exact (TRANS (@lem3607006 A s) (@lem3607013 A s)). Qed.
Lemma lem3607015 {A : Type'} (P : type686 A) : (term47 A P) = (term48 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3607016 {A : Type'} : (term10 A) = (term56 A).
Proof. exact (@lem3607015 A (term42 A)). Qed.
Lemma lem3607017 {A : Type'} (s : A -> Prop) : (term57 A s) = (term41 A s).
Proof. exact (eq_refl (term57 A s)). Qed.
Lemma lem3607018 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3607019 {A : Type'} (s : A -> Prop) : (term58 A s) = (term49 A s).
Proof. exact (MK_COMB (@lem3607018) (@lem3607017 A s)). Qed.
Lemma lem3607020 {A : Type'} (s : A -> Prop) : (term58 A s) = (term55 A s).
Proof. exact (TRANS (@lem3607019 A s) (@lem3607014 A s)). Qed.
Lemma lem3607021 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607020 A s)). Qed.
Lemma lem3607022 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3607023 {A : Type'} : (term56 A) = (term61 A).
Proof. exact (MK_COMB (@lem3607022 A) (@lem3607021 A)). Qed.
Lemma lem3607080 {A : Type'} : (term10 A) = (term61 A).
Proof. exact (TRANS (@lem3607016 A) (@lem3607023 A)). Qed.
Lemma lem3607081 {A : Type'} (h1 : term10 A) : term61 A.
Proof. exact (EQ_MP (@lem3607080 A) (@lem3606991 A h1)). Qed.
Lemma lem3607088 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term63 A s t).
Proof. exact (@lem17045 (@FINITE A t) (@SUBSET A s t)). Qed.
Lemma lem3607089 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3607090) (@lem3607088 A s t)). Qed.
Lemma lem3607092 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term66 A t s) = (term67 A t s).
Proof. exact (MK_COMB (@lem3607091 A s t) (@lem3607089 A s)). Qed.
Lemma lem3607093 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term35 A t s) = (term66 A t s).
Proof. exact (@lem17265 (term68 A s t) (@FINITE A s)). Qed.
Lemma lem3607094 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term35 A t s) = (term67 A t s).
Proof. exact (TRANS (@lem3607093 A t s) (@lem3607092 A t s)). Qed.
Lemma lem3607095 {A : Type'} (s : A -> Prop) : (term36 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607094 A t s)). Qed.
Lemma lem3607096 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607097 {A : Type'} (s : A -> Prop) : (term37 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607096 A) (@lem3607095 A s)). Qed.
Lemma lem3607098 {A : Type'} : (term38 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607097 A s)). Qed.
Lemma lem3607099 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607100 {A : Type'} : (term12 A) = (term72 A).
Proof. exact (MK_COMB (@lem3607099 A) (@lem3607098 A)). Qed.
Lemma lem3607126 {A : Type'} (P : A -> Prop) (Q : Prop) : (term73 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3607127 {A : Type'} (P : type686 A) (Q : Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (@lem3607126 (A -> Prop) P Q). Qed.
Lemma lem3607128 {A : Type'} (s : A -> Prop) : (term77 A s) = (term78 A s).
Proof. exact (@lem3607127 A (term79 A s) (@FINITE A s)). Qed.
Lemma lem3607129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607131 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3607130) (@lem3607129 A s t)). Qed.
Lemma lem3607132 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607133 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term82 A t s) = (term67 A t s).
Proof. exact (MK_COMB (@lem3607131 A s t) (@lem3607132 A s)). Qed.
Lemma lem3607134 {A : Type'} (s : A -> Prop) : (term83 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607133 A t s)). Qed.
Lemma lem3607135 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607136 {A : Type'} (s : A -> Prop) : (term77 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607135 A) (@lem3607134 A s)). Qed.
Lemma lem3607137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3607138 {A : Type'} (s : A -> Prop) : (term84 A s) = (term85 A s).
Proof. exact (MK_COMB (@lem3607137) (@lem3607136 A s)). Qed.
Lemma lem3607139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607140 {A : Type'} (s : A -> Prop) : (term86 A s) = (term79 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607139 A s t)). Qed.
Lemma lem3607141 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607142 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (MK_COMB (@lem3607141 A) (@lem3607140 A s)). Qed.
Lemma lem3607143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607144 {A : Type'} (s : A -> Prop) : (term89 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem3607143) (@lem3607142 A s)). Qed.
Lemma lem3607145 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607146 {A : Type'} (s : A -> Prop) : (term78 A s) = (term91 A s).
Proof. exact (MK_COMB (@lem3607144 A s) (@lem3607145 A s)). Qed.
Lemma lem3607147 {A : Type'} (s : A -> Prop) : ((term77 A s) = (term78 A s)) = ((term70 A s) = (term91 A s)).
Proof. exact (MK_COMB (@lem3607138 A s) (@lem3607146 A s)). Qed.
Lemma lem3607148 {A : Type'} (s : A -> Prop) : (term70 A s) = (term91 A s).
Proof. exact (EQ_MP (@lem3607147 A s) (@lem3607128 A s)). Qed.
Lemma lem3607197 {A : Type'} : (term71 A) = (term92 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607148 A s)). Qed.
Lemma lem3607198 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607233 {A : Type'} : (term72 A) = (term93 A).
Proof. exact (MK_COMB (@lem3607198 A) (@lem3607197 A)). Qed.
Lemma lem3607234 {A : Type'} : (term12 A) = (term93 A).
Proof. exact (TRANS (@lem3607100 A) (@lem3607233 A)). Qed.
Lemma lem3607235 {A : Type'} (h1 : term12 A) : term93 A.
Proof. exact (EQ_MP (@lem3607234 A) (@lem3606992 A h1)). Qed.
Lemma lem3607236 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (eq_refl (term29 A t s)). Qed.
Lemma lem3607237 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607236 A t s)). Qed.
Lemma lem3607238 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607239 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3607238 A) (@lem3607237 A s)). Qed.
Lemma lem3607240 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607239 A s)). Qed.
Lemma lem3607241 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607242 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3607241 A) (@lem3607240 A)). Qed.
Lemma lem3607243 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (eq_refl (term24 A t s)). Qed.
Lemma lem3607244 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607243 A t s)). Qed.
Lemma lem3607245 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607246 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3607245 A) (@lem3607244 A s)). Qed.
Lemma lem3607247 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607246 A s)). Qed.
Lemma lem3607248 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607249 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3607248 A) (@lem3607247 A)). Qed.
Lemma lem3607250 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3607251 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3607250) (@lem3607242 A)). Qed.
Lemma lem3607272 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3607251 A) (@lem3607249 A)). Qed.
Lemma lem3607273 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (EQ_MP (@lem3607272 A) (@lem3606993 A h1)). Qed.
Lemma lem3607274 {A : Type'} (s : A -> Prop) (h1 : term55 A s) : term55 A s.
Proof. exact (h1). Qed.
Lemma lem3607278 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607293 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term63 A s t) = (term63 A s t).
Proof. exact (eq_refl (term63 A s t)). Qed.
Lemma lem3607294 {A : Type'} (s : A -> Prop) : (term79 A s) = (term79 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607293 A s t)). Qed.
Lemma lem3607295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607296 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (MK_COMB (@lem3607295 A) (@lem3607294 A s)). Qed.
Lemma lem3607297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607298 {A : Type'} (s : A -> Prop) : (term90 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem3607297) (@lem3607296 A s)). Qed.
Lemma lem3607299 {A : Type'} (s : A -> Prop) : (term91 A s) = (term91 A s).
Proof. exact (MK_COMB (@lem3607298 A s) (@lem3607278 A s)). Qed.
Lemma lem3607300 {A : Type'} : (term92 A) = (term92 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607299 A s)). Qed.
Lemma lem3607301 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607302 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (MK_COMB (@lem3607301 A) (@lem3607300 A)). Qed.
Lemma lem3607303 {A : Type'} (h1 : term12 A) : term93 A.
Proof. exact (EQ_MP (@lem3607302 A) (@lem3607235 A h1)). Qed.
Lemma lem3607312 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (eq_refl (term24 A t s)). Qed.
Lemma lem3607313 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607312 A t s)). Qed.
Lemma lem3607314 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607315 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3607314 A) (@lem3607313 A s)). Qed.
Lemma lem3607316 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607315 A s)). Qed.
Lemma lem3607317 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607318 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3607317 A) (@lem3607316 A)). Qed.
Lemma lem3607327 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (eq_refl (term29 A t s)). Qed.
Lemma lem3607328 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607327 A t s)). Qed.
Lemma lem3607329 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607330 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3607329 A) (@lem3607328 A s)). Qed.
Lemma lem3607331 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607330 A s)). Qed.
Lemma lem3607332 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607333 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3607332 A) (@lem3607331 A)). Qed.
Lemma lem3607334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3607335 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3607334) (@lem3607333 A)). Qed.
Lemma lem3607336 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3607335 A) (@lem3607318 A)). Qed.
Lemma lem3607337 {A : Type'} (h1 : term11 A) : term11 A.
Proof. exact (EQ_MP (@lem3607336 A) (@lem3607273 A h1)). Qed.
Lemma lem3607359 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term44 A s t.
Proof. exact (h1). Qed.
Lemma lem3607361 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term45 A s t.
Proof. exact (proj1 (@lem3607359 A s t h1)). Qed.
Lemma lem3607362 {A : Type'} (h1 : term11 A) : term28 A.
Proof. exact (proj2 (@lem3607337 A h1)). Qed.
Lemma lem3607363 {A : Type'} (h1 : term11 A) : term33 A.
Proof. exact (proj1 (@lem3607337 A h1)). Qed.
Lemma lem3607367 {A : Type'} (P : A -> Prop) (Q : Prop) : (term74 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3607368 {A : Type'} (P : type686 A) (Q : Prop) : (term76 A P Q) = (term75 A P Q).
Proof. exact (@lem3607367 (A -> Prop) P Q). Qed.
Lemma lem3607369 {A : Type'} (s : A -> Prop) : (term78 A s) = (term77 A s).
Proof. exact (@lem3607368 A (term79 A s) (@FINITE A s)). Qed.
Lemma lem3607370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607371 {A : Type'} (s : A -> Prop) : (term86 A s) = (term79 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607370 A s t)). Qed.
Lemma lem3607372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607373 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (MK_COMB (@lem3607372 A) (@lem3607371 A s)). Qed.
Lemma lem3607374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607375 {A : Type'} (s : A -> Prop) : (term89 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem3607374) (@lem3607373 A s)). Qed.
Lemma lem3607376 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607377 {A : Type'} (s : A -> Prop) : (term78 A s) = (term91 A s).
Proof. exact (MK_COMB (@lem3607375 A s) (@lem3607376 A s)). Qed.
Lemma lem3607378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3607379 {A : Type'} (s : A -> Prop) : (term94 A s) = (term95 A s).
Proof. exact (MK_COMB (@lem3607378) (@lem3607377 A s)). Qed.
Lemma lem3607380 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607382 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3607381) (@lem3607380 A s t)). Qed.
Lemma lem3607383 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607384 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term82 A t s) = (term67 A t s).
Proof. exact (MK_COMB (@lem3607382 A s t) (@lem3607383 A s)). Qed.
Lemma lem3607385 {A : Type'} (s : A -> Prop) : (term83 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607384 A t s)). Qed.
Lemma lem3607386 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607387 {A : Type'} (s : A -> Prop) : (term77 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607386 A) (@lem3607385 A s)). Qed.
Lemma lem3607388 {A : Type'} (s : A -> Prop) : ((term78 A s) = (term77 A s)) = ((term91 A s) = (term70 A s)).
Proof. exact (MK_COMB (@lem3607379 A s) (@lem3607387 A s)). Qed.
Lemma lem3607389 {A : Type'} (s : A -> Prop) : (term91 A s) = (term70 A s).
Proof. exact (EQ_MP (@lem3607388 A s) (@lem3607369 A s)). Qed.
Lemma lem3607390 {A : Type'} : (term92 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607389 A s)). Qed.
Lemma lem3607391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607392 {A : Type'} : (term93 A) = (term72 A).
Proof. exact (MK_COMB (@lem3607391 A) (@lem3607390 A)). Qed.
Lemma lem3607405 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term67 A t s) = (term67 A t s).
Proof. exact (eq_refl (term67 A t s)). Qed.
Lemma lem3607406 {A : Type'} (s : A -> Prop) : (term69 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607405 A t s)). Qed.
Lemma lem3607407 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607408 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607407 A) (@lem3607406 A s)). Qed.
Lemma lem3607409 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607408 A s)). Qed.
Lemma lem3607410 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607411 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (MK_COMB (@lem3607410 A) (@lem3607409 A)). Qed.
Lemma lem3607412 {A : Type'} : (term93 A) = (term72 A).
Proof. exact (TRANS (@lem3607392 A) (@lem3607411 A)). Qed.
Lemma lem3607413 {A : Type'} (h1 : term12 A) : term72 A.
Proof. exact (EQ_MP (@lem3607412 A) (@lem3607303 A h1)). Qed.
Lemma lem3607419 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term29 A t s) = (term29 A t s).
Proof. exact (eq_refl (term29 A t s)). Qed.
Lemma lem3607420 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607419 A t s)). Qed.
Lemma lem3607421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607422 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (MK_COMB (@lem3607421 A) (@lem3607420 A s)). Qed.
Lemma lem3607423 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607422 A s)). Qed.
Lemma lem3607424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607426 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem3607424 A) (@lem3607423 A)). Qed.
Lemma lem3607427 {A : Type'} (h1 : term11 A) : term33 A.
Proof. exact (EQ_MP (@lem3607426 A) (@lem3607363 A h1)). Qed.
Lemma lem3607441 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3607443 {A : Type'} (P : A -> Prop) (Q : Prop) : (term74 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3607444 {A : Type'} (P : type686 A) (Q : Prop) : (term76 A P Q) = (term75 A P Q).
Proof. exact (@lem3607443 (A -> Prop) P Q). Qed.
Lemma lem3607445 {A : Type'} (s : A -> Prop) : (term78 A s) = (term77 A s).
Proof. exact (@lem3607444 A (term79 A s) (@FINITE A s)). Qed.
Lemma lem3607446 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607447 {A : Type'} (s : A -> Prop) : (term86 A s) = (term79 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607446 A s t)). Qed.
Lemma lem3607448 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607449 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (MK_COMB (@lem3607448 A) (@lem3607447 A s)). Qed.
Lemma lem3607450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607451 {A : Type'} (s : A -> Prop) : (term89 A s) = (term90 A s).
Proof. exact (MK_COMB (@lem3607450) (@lem3607449 A s)). Qed.
Lemma lem3607452 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607453 {A : Type'} (s : A -> Prop) : (term78 A s) = (term91 A s).
Proof. exact (MK_COMB (@lem3607451 A s) (@lem3607452 A s)). Qed.
Lemma lem3607454 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3607455 {A : Type'} (s : A -> Prop) : (term94 A s) = (term95 A s).
Proof. exact (MK_COMB (@lem3607454) (@lem3607453 A s)). Qed.
Lemma lem3607456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term63 A s t).
Proof. exact (eq_refl (term80 A s t)). Qed.
Lemma lem3607457 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3607458 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term65 A s t).
Proof. exact (MK_COMB (@lem3607457) (@lem3607456 A s t)). Qed.
Lemma lem3607459 {A : Type'} (s : A -> Prop) : (@FINITE A s) = (@FINITE A s).
Proof. exact (eq_refl (@FINITE A s)). Qed.
Lemma lem3607460 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term82 A t s) = (term67 A t s).
Proof. exact (MK_COMB (@lem3607458 A s t) (@lem3607459 A s)). Qed.
Lemma lem3607461 {A : Type'} (s : A -> Prop) : (term83 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607460 A t s)). Qed.
Lemma lem3607462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607463 {A : Type'} (s : A -> Prop) : (term77 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607462 A) (@lem3607461 A s)). Qed.
Lemma lem3607464 {A : Type'} (s : A -> Prop) : ((term78 A s) = (term77 A s)) = ((term91 A s) = (term70 A s)).
Proof. exact (MK_COMB (@lem3607455 A s) (@lem3607463 A s)). Qed.
Lemma lem3607465 {A : Type'} (s : A -> Prop) : (term91 A s) = (term70 A s).
Proof. exact (EQ_MP (@lem3607464 A s) (@lem3607445 A s)). Qed.
Lemma lem3607466 {A : Type'} : (term92 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607465 A s)). Qed.
Lemma lem3607467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607468 {A : Type'} : (term93 A) = (term72 A).
Proof. exact (MK_COMB (@lem3607467 A) (@lem3607466 A)). Qed.
Lemma lem3607481 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term67 A t s) = (term67 A t s).
Proof. exact (eq_refl (term67 A t s)). Qed.
Lemma lem3607482 {A : Type'} (s : A -> Prop) : (term69 A s) = (term69 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607481 A t s)). Qed.
Lemma lem3607483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607484 {A : Type'} (s : A -> Prop) : (term70 A s) = (term70 A s).
Proof. exact (MK_COMB (@lem3607483 A) (@lem3607482 A s)). Qed.
Lemma lem3607485 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607484 A s)). Qed.
Lemma lem3607486 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607487 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (MK_COMB (@lem3607486 A) (@lem3607485 A)). Qed.
Lemma lem3607488 {A : Type'} : (term93 A) = (term72 A).
Proof. exact (TRANS (@lem3607468 A) (@lem3607487 A)). Qed.
Lemma lem3607489 {A : Type'} (h1 : term12 A) : term72 A.
Proof. exact (EQ_MP (@lem3607488 A) (@lem3607303 A h1)). Qed.
Lemma lem3607505 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (eq_refl (term24 A t s)). Qed.
Lemma lem3607506 {A : Type'} (s : A -> Prop) : (term25 A s) = (term25 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3607505 A t s)). Qed.
Lemma lem3607507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607508 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3607507 A) (@lem3607506 A s)). Qed.
Lemma lem3607509 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3607508 A s)). Qed.
Lemma lem3607510 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3607512 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3607510 A) (@lem3607509 A)). Qed.
Lemma lem3607513 {A : Type'} (h1 : term11 A) : term28 A.
Proof. exact (EQ_MP (@lem3607512 A) (@lem3607362 A h1)). Qed.
Lemma lem3607517 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3607518 {A : Type'} (_39085 : A -> Prop) (h1 : term12 A) : term96 A _39085.
Proof. exact (@lem3607413 A h1 _39085). Qed.
Lemma lem3607519 {A : Type'} (_39085 : A -> Prop) : (term96 A _39085) = (term70 A _39085).
Proof. exact (eq_refl (term96 A _39085)). Qed.
Lemma lem3607520 {A : Type'} (_39085 : A -> Prop) (h1 : term12 A) : term70 A _39085.
Proof. exact (EQ_MP (@lem3607519 A _39085) (@lem3607518 A _39085 h1)). Qed.
Lemma lem3607521 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) (h1 : term12 A) : term97 A _39085 _39086.
Proof. exact (@lem3607520 A _39085 h1 _39086). Qed.
Lemma lem3607522 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) : (term97 A _39085 _39086) = (term67 A _39086 _39085).
Proof. exact (eq_refl (term97 A _39085 _39086)). Qed.
Lemma lem3607523 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) (h1 : term12 A) : term67 A _39086 _39085.
Proof. exact (EQ_MP (@lem3607522 A _39086 _39085) (@lem3607521 A _39085 _39086 h1)). Qed.
Lemma lem3607524 {A : Type'} (_39087 : A -> Prop) (h1 : term11 A) : term98 A _39087.
Proof. exact (@lem3607427 A h1 _39087). Qed.
Lemma lem3607525 {A : Type'} (_39087 : A -> Prop) : (term98 A _39087) = (term31 A _39087).
Proof. exact (eq_refl (term98 A _39087)). Qed.
Lemma lem3607526 {A : Type'} (_39087 : A -> Prop) (h1 : term11 A) : term31 A _39087.
Proof. exact (EQ_MP (@lem3607525 A _39087) (@lem3607524 A _39087 h1)). Qed.
Lemma lem3607527 {A : Type'} (_39087 : A -> Prop) (_39088 : A -> Prop) (h1 : term11 A) : term99 A _39087 _39088.
Proof. exact (@lem3607526 A _39087 h1 _39088). Qed.
Lemma lem3607528 {A : Type'} (_39088 : A -> Prop) (_39087 : A -> Prop) : (term99 A _39087 _39088) = (term29 A _39088 _39087).
Proof. exact (eq_refl (term99 A _39087 _39088)). Qed.
Lemma lem3607536 {A : Type'} (_39091 : A -> Prop) (h1 : term12 A) : term96 A _39091.
Proof. exact (@lem3607489 A h1 _39091). Qed.
Lemma lem3607537 {A : Type'} (_39091 : A -> Prop) : (term96 A _39091) = (term70 A _39091).
Proof. exact (eq_refl (term96 A _39091)). Qed.
Lemma lem3607538 {A : Type'} (_39091 : A -> Prop) (h1 : term12 A) : term70 A _39091.
Proof. exact (EQ_MP (@lem3607537 A _39091) (@lem3607536 A _39091 h1)). Qed.
Lemma lem3607539 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) (h1 : term12 A) : term97 A _39091 _39092.
Proof. exact (@lem3607538 A _39091 h1 _39092). Qed.
Lemma lem3607540 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) : (term97 A _39091 _39092) = (term67 A _39092 _39091).
Proof. exact (eq_refl (term97 A _39091 _39092)). Qed.
Lemma lem3607541 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) (h1 : term12 A) : term67 A _39092 _39091.
Proof. exact (EQ_MP (@lem3607540 A _39092 _39091) (@lem3607539 A _39091 _39092 h1)). Qed.
Lemma lem3607548 {A : Type'} (_39095 : A -> Prop) (h1 : term11 A) : term100 A _39095.
Proof. exact (@lem3607513 A h1 _39095). Qed.
Lemma lem3607549 {A : Type'} (_39095 : A -> Prop) : (term100 A _39095) = (term26 A _39095).
Proof. exact (eq_refl (term100 A _39095)). Qed.
Lemma lem3607550 {A : Type'} (_39095 : A -> Prop) (h1 : term11 A) : term26 A _39095.
Proof. exact (EQ_MP (@lem3607549 A _39095) (@lem3607548 A _39095 h1)). Qed.
Lemma lem3607551 {A : Type'} (_39095 : A -> Prop) (_39096 : A -> Prop) (h1 : term11 A) : term101 A _39095 _39096.
Proof. exact (@lem3607550 A _39095 h1 _39096). Qed.
Lemma lem3607552 {A : Type'} (_39096 : A -> Prop) (_39095 : A -> Prop) : (term101 A _39095 _39096) = (term24 A _39096 _39095).
Proof. exact (eq_refl (term101 A _39095 _39096)). Qed.
Lemma lem3607564 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) : (term67 A _39086 _39085) = (term102 A _39086 _39085).
Proof. exact (@lem3606782 (term103 A _39086) (term104 A _39085 _39086) (@FINITE A _39085)). Qed.
Lemma lem3607565 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) (h1 : term12 A) : term102 A _39086 _39085.
Proof. exact (EQ_MP (@lem3607564 A _39086 _39085) (@lem3607523 A _39086 _39085 h1)). Qed.
Lemma lem3607567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term105 A s t.
Proof. exact (proj2 (@lem3607359 A s t h1)). Qed.
Lemma lem3607573 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3607584 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) : (term67 A _39092 _39091) = (term102 A _39092 _39091).
Proof. exact (@lem3606782 (term103 A _39092) (term104 A _39091 _39092) (@FINITE A _39091)). Qed.
Lemma lem3607585 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) (h1 : term12 A) : term102 A _39092 _39091.
Proof. exact (EQ_MP (@lem3607584 A _39092 _39091) (@lem3607541 A _39092 _39091 h1)). Qed.
Lemma lem3607587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term105 A s t.
Proof. exact (proj2 (@lem3607359 A s t h1)). Qed.
Lemma lem3607593 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3607595 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3607596 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term106 A s.
Proof. exact (fun h0 : term103 A s => @lem3607595 A s h1). Qed.
Lemma lem3607598 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607599 {A : Type'} (s : A -> Prop) : (term106 A s) = (@FINITE A s).
Proof. exact (@lem3607598 (@FINITE A s)). Qed.
Lemma lem3607600 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem3607599 A s) (@lem3607596 A s h1)). Qed.
Lemma lem3607602 {A : Type'} (_39088 : A -> Prop) (_39087 : A -> Prop) (h1 : term11 A) : term29 A _39088 _39087.
Proof. exact (EQ_MP (@lem3607528 A _39088 _39087) (@lem3607527 A _39087 _39088 h1)). Qed.
Lemma lem3607603 {A : Type'} (_39088 : A -> Prop) (_39087 : A -> Prop) (h1 : term11 A) : term29 A _39088 _39087.
Proof. exact (@lem3607602 A _39088 _39087 h1). Qed.
Lemma lem3607604 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term29 A t s.
Proof. exact (@lem3607603 A t s h1). Qed.
Lemma lem3607605 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term108 A t s.
Proof. exact (fun h0 : term109 A t s => @lem3607604 A t s h1). Qed.
Lemma lem3607607 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607608 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term108 A t s) = (term29 A t s).
Proof. exact (@lem3607607 (term29 A t s)). Qed.
Lemma lem3607609 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term11 A) : term29 A t s.
Proof. exact (EQ_MP (@lem3607608 A t s) (@lem3607605 A t s h1)). Qed.
Lemma lem3607625 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3607626 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term110 A _39086 _39085) = (term111 A _39085 _39086).
Proof. exact (@lem3607625 (@FINITE A _39085) (term104 A _39085 _39086)). Qed.
Lemma lem3607632 {A : Type'} (_39086 : A -> Prop) : (term112 A _39086) = (term112 A _39086).
Proof. exact (eq_refl (term112 A _39086)). Qed.
Lemma lem3607633 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term102 A _39086 _39085) = (term113 A _39085 _39086).
Proof. exact (MK_COMB (@lem3607632 A _39086) (@lem3607626 A _39085 _39086)). Qed.
Lemma lem3607637 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3607638 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term113 A _39085 _39086) = (term114 A _39085 _39086).
Proof. exact (@lem3607637 (@FINITE A _39085) (term103 A _39086) (term104 A _39085 _39086)). Qed.
Lemma lem3607654 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term102 A _39086 _39085) = (term114 A _39085 _39086).
Proof. exact (TRANS (@lem3607633 A _39085 _39086) (@lem3607638 A _39085 _39086)). Qed.
Lemma lem3607655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3607656 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term115 A _39086 _39085) = (term116 A _39085 _39086).
Proof. exact (MK_COMB (@lem3607655) (@lem3607654 A _39085 _39086)). Qed.
Lemma lem3607672 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term114 A _39085 _39086) = (term114 A _39085 _39086).
Proof. exact (eq_refl (term114 A _39085 _39086)). Qed.
Lemma lem3607673 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : ((term102 A _39086 _39085) = (term114 A _39085 _39086)) = ((term114 A _39085 _39086) = (term114 A _39085 _39086)).
Proof. exact (MK_COMB (@lem3607656 A _39085 _39086) (@lem3607672 A _39085 _39086)). Qed.
Lemma lem3607675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3607676 (x : Prop) : (x = x) = True.
Proof. exact (@lem3607675 Prop x). Qed.
Lemma lem3607677 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : ((term114 A _39085 _39086) = (term114 A _39085 _39086)) = True.
Proof. exact (@lem3607676 (term114 A _39085 _39086)). Qed.
Lemma lem3607678 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : ((term102 A _39086 _39085) = (term114 A _39085 _39086)) = True.
Proof. exact (TRANS (@lem3607673 A _39085 _39086) (@lem3607677 A _39085 _39086)). Qed.
Lemma lem3607679 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : True = ((term102 A _39086 _39085) = (term114 A _39085 _39086)).
Proof. exact (SYM (@lem3607678 A _39085 _39086)). Qed.
Lemma lem3607680 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term102 A _39086 _39085) = (term114 A _39085 _39086).
Proof. exact (EQ_MP (@lem3607679 A _39085 _39086) (@lem0)). Qed.
Lemma lem3607681 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) (h1 : term12 A) : term114 A _39085 _39086.
Proof. exact (EQ_MP (@lem3607680 A _39085 _39086) (@lem3607565 A _39086 _39085 h1)). Qed.
Lemma lem3607683 (b : Prop) (a : Prop) : (a \/ b) = (term117 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3607684 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) : (term114 A _39085 _39086) = (term118 A _39086 _39085).
Proof. exact (@lem3607683 (term63 A _39085 _39086) (@FINITE A _39085)). Qed.
Lemma lem3607686 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3607687 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term121 A _39085 _39086) = (term122 A _39085 _39086).
Proof. exact (@lem3607686 (term103 A _39086) (term104 A _39085 _39086)). Qed.
Lemma lem3607689 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3607690 {A : Type'} (_39086 : A -> Prop) : (term124 A _39086) = (@FINITE A _39086).
Proof. exact (@lem3607689 (@FINITE A _39086)). Qed.
Lemma lem3607691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3607692 {A : Type'} (_39086 : A -> Prop) : (term125 A _39086) = (term126 A _39086).
Proof. exact (MK_COMB (@lem3607691) (@lem3607690 A _39086)). Qed.
Lemma lem3607694 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3607695 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term127 A _39085 _39086) = (@SUBSET A _39085 _39086).
Proof. exact (@lem3607694 (@SUBSET A _39085 _39086)). Qed.
Lemma lem3607696 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term122 A _39085 _39086) = (term68 A _39085 _39086).
Proof. exact (MK_COMB (@lem3607692 A _39086) (@lem3607695 A _39085 _39086)). Qed.
Lemma lem3607697 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term121 A _39085 _39086) = (term68 A _39085 _39086).
Proof. exact (TRANS (@lem3607687 A _39085 _39086) (@lem3607696 A _39085 _39086)). Qed.
Lemma lem3607698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3607699 {A : Type'} (_39085 : A -> Prop) (_39086 : A -> Prop) : (term128 A _39085 _39086) = (term129 A _39085 _39086).
Proof. exact (MK_COMB (@lem3607698) (@lem3607697 A _39085 _39086)). Qed.
Lemma lem3607700 {A : Type'} (_39085 : A -> Prop) : (@FINITE A _39085) = (@FINITE A _39085).
Proof. exact (eq_refl (@FINITE A _39085)). Qed.
Lemma lem3607701 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) : (term118 A _39086 _39085) = (term35 A _39086 _39085).
Proof. exact (MK_COMB (@lem3607699 A _39085 _39086) (@lem3607700 A _39085)). Qed.
Lemma lem3607702 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) : (term114 A _39085 _39086) = (term35 A _39086 _39085).
Proof. exact (TRANS (@lem3607684 A _39086 _39085) (@lem3607701 A _39086 _39085)). Qed.
Lemma lem3607704 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term11 A) : term130 A t s.
Proof. exact (conj (@lem3607600 A s h1) (@lem3607609 A t s h2)). Qed.
Lemma lem3607706 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) (h1 : term12 A) : term35 A _39086 _39085.
Proof. exact (EQ_MP (@lem3607702 A _39086 _39085) (@lem3607681 A _39085 _39086 h1)). Qed.
Lemma lem3607707 {A : Type'} (_39086 : A -> Prop) (_39085 : A -> Prop) (h1 : term12 A) : term35 A _39086 _39085.
Proof. exact (@lem3607706 A _39086 _39085 h1). Qed.
Lemma lem3607708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) : term131 A s t.
Proof. exact (@lem3607707 A s (@INTER A s t) h1). Qed.
Lemma lem3607711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) : term46 A s t.
Proof. exact (@lem3607708 A s t h1 (@lem3607704 A t s h2 h3)). Qed.
Lemma lem3607712 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) : term46 A s t.
Proof. exact (@lem3607711 A t s h1 h2 h3). Qed.
Lemma lem3607713 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) : term132 A s t.
Proof. exact (fun h0 : term105 A s t => @lem3607712 A t s h1 h2 h3). Qed.
Lemma lem3607715 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607716 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term46 A s t).
Proof. exact (@lem3607715 (term46 A s t)). Qed.
Lemma lem3607717 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) : term46 A s t.
Proof. exact (EQ_MP (@lem3607716 A s t) (@lem3607713 A t s h1 h2 h3)). Qed.
Lemma lem3607720 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3607722 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term133 A s t).
Proof. exact (@lem3607720 (term46 A s t)). Qed.
Lemma lem3607725 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term133 A s t.
Proof. exact (EQ_MP (@lem3607722 A s t) (@lem3607567 A s t h1)). Qed.
Lemma lem3607728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (@lem3607725 A s t h4 (@lem3607717 A t s h1 h2 h3)). Qed.
Lemma lem3607729 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : term134.
Proof. exact (fun h0 : ~ False => @lem3607728 A s t h1 h2 h3 h4). Qed.
Lemma lem3607731 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607732 : term134 = False.
Proof. exact (@lem3607731 False). Qed.
Lemma lem3607733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607732) (@lem3607729 A s t h1 h2 h3 h4)). Qed.
Lemma lem3607735 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3607736 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : term106 A t.
Proof. exact (fun h0 : term103 A t => @lem3607735 A t h1). Qed.
Lemma lem3607738 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607739 {A : Type'} (t : A -> Prop) : (term106 A t) = (@FINITE A t).
Proof. exact (@lem3607738 (@FINITE A t)). Qed.
Lemma lem3607740 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (EQ_MP (@lem3607739 A t) (@lem3607736 A t h1)). Qed.
Lemma lem3607742 {A : Type'} (_39096 : A -> Prop) (_39095 : A -> Prop) (h1 : term11 A) : term24 A _39096 _39095.
Proof. exact (EQ_MP (@lem3607552 A _39096 _39095) (@lem3607551 A _39095 _39096 h1)). Qed.
Lemma lem3607743 {A : Type'} (_39096 : A -> Prop) (_39095 : A -> Prop) (h1 : term11 A) : term24 A _39096 _39095.
Proof. exact (@lem3607742 A _39096 _39095 h1). Qed.
Lemma lem3607744 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) : term24 A s t.
Proof. exact (@lem3607743 A s t h1). Qed.
Lemma lem3607745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) : term135 A s t.
Proof. exact (fun h0 : term136 A s t => @lem3607744 A s t h1). Qed.
Lemma lem3607747 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607748 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term24 A s t).
Proof. exact (@lem3607747 (term24 A s t)). Qed.
Lemma lem3607749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term11 A) : term24 A s t.
Proof. exact (EQ_MP (@lem3607748 A s t) (@lem3607745 A s t h1)). Qed.
Lemma lem3607765 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3607766 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term110 A _39092 _39091) = (term111 A _39091 _39092).
Proof. exact (@lem3607765 (@FINITE A _39091) (term104 A _39091 _39092)). Qed.
Lemma lem3607772 {A : Type'} (_39092 : A -> Prop) : (term112 A _39092) = (term112 A _39092).
Proof. exact (eq_refl (term112 A _39092)). Qed.
Lemma lem3607773 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term102 A _39092 _39091) = (term113 A _39091 _39092).
Proof. exact (MK_COMB (@lem3607772 A _39092) (@lem3607766 A _39091 _39092)). Qed.
Lemma lem3607777 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3607778 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term113 A _39091 _39092) = (term114 A _39091 _39092).
Proof. exact (@lem3607777 (@FINITE A _39091) (term103 A _39092) (term104 A _39091 _39092)). Qed.
Lemma lem3607794 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term102 A _39092 _39091) = (term114 A _39091 _39092).
Proof. exact (TRANS (@lem3607773 A _39091 _39092) (@lem3607778 A _39091 _39092)). Qed.
Lemma lem3607795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3607796 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term115 A _39092 _39091) = (term116 A _39091 _39092).
Proof. exact (MK_COMB (@lem3607795) (@lem3607794 A _39091 _39092)). Qed.
Lemma lem3607812 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term114 A _39091 _39092) = (term114 A _39091 _39092).
Proof. exact (eq_refl (term114 A _39091 _39092)). Qed.
Lemma lem3607813 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : ((term102 A _39092 _39091) = (term114 A _39091 _39092)) = ((term114 A _39091 _39092) = (term114 A _39091 _39092)).
Proof. exact (MK_COMB (@lem3607796 A _39091 _39092) (@lem3607812 A _39091 _39092)). Qed.
Lemma lem3607815 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3607816 (x : Prop) : (x = x) = True.
Proof. exact (@lem3607815 Prop x). Qed.
Lemma lem3607817 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : ((term114 A _39091 _39092) = (term114 A _39091 _39092)) = True.
Proof. exact (@lem3607816 (term114 A _39091 _39092)). Qed.
Lemma lem3607818 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : ((term102 A _39092 _39091) = (term114 A _39091 _39092)) = True.
Proof. exact (TRANS (@lem3607813 A _39091 _39092) (@lem3607817 A _39091 _39092)). Qed.
Lemma lem3607819 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : True = ((term102 A _39092 _39091) = (term114 A _39091 _39092)).
Proof. exact (SYM (@lem3607818 A _39091 _39092)). Qed.
Lemma lem3607820 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term102 A _39092 _39091) = (term114 A _39091 _39092).
Proof. exact (EQ_MP (@lem3607819 A _39091 _39092) (@lem0)). Qed.
Lemma lem3607821 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) (h1 : term12 A) : term114 A _39091 _39092.
Proof. exact (EQ_MP (@lem3607820 A _39091 _39092) (@lem3607585 A _39092 _39091 h1)). Qed.
Lemma lem3607823 (b : Prop) (a : Prop) : (a \/ b) = (term117 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3607824 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) : (term114 A _39091 _39092) = (term118 A _39092 _39091).
Proof. exact (@lem3607823 (term63 A _39091 _39092) (@FINITE A _39091)). Qed.
Lemma lem3607826 (a : Prop) (b : Prop) : (term119 a b) = (term120 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3607827 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term121 A _39091 _39092) = (term122 A _39091 _39092).
Proof. exact (@lem3607826 (term103 A _39092) (term104 A _39091 _39092)). Qed.
Lemma lem3607829 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3607830 {A : Type'} (_39092 : A -> Prop) : (term124 A _39092) = (@FINITE A _39092).
Proof. exact (@lem3607829 (@FINITE A _39092)). Qed.
Lemma lem3607831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3607832 {A : Type'} (_39092 : A -> Prop) : (term125 A _39092) = (term126 A _39092).
Proof. exact (MK_COMB (@lem3607831) (@lem3607830 A _39092)). Qed.
Lemma lem3607834 (a : Prop) : (term123 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3607835 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term127 A _39091 _39092) = (@SUBSET A _39091 _39092).
Proof. exact (@lem3607834 (@SUBSET A _39091 _39092)). Qed.
Lemma lem3607836 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term122 A _39091 _39092) = (term68 A _39091 _39092).
Proof. exact (MK_COMB (@lem3607832 A _39092) (@lem3607835 A _39091 _39092)). Qed.
Lemma lem3607837 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term121 A _39091 _39092) = (term68 A _39091 _39092).
Proof. exact (TRANS (@lem3607827 A _39091 _39092) (@lem3607836 A _39091 _39092)). Qed.
Lemma lem3607838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3607839 {A : Type'} (_39091 : A -> Prop) (_39092 : A -> Prop) : (term128 A _39091 _39092) = (term129 A _39091 _39092).
Proof. exact (MK_COMB (@lem3607838) (@lem3607837 A _39091 _39092)). Qed.
Lemma lem3607840 {A : Type'} (_39091 : A -> Prop) : (@FINITE A _39091) = (@FINITE A _39091).
Proof. exact (eq_refl (@FINITE A _39091)). Qed.
Lemma lem3607841 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) : (term118 A _39092 _39091) = (term35 A _39092 _39091).
Proof. exact (MK_COMB (@lem3607839 A _39091 _39092) (@lem3607840 A _39091)). Qed.
Lemma lem3607842 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) : (term114 A _39091 _39092) = (term35 A _39092 _39091).
Proof. exact (TRANS (@lem3607824 A _39092 _39091) (@lem3607841 A _39092 _39091)). Qed.
Lemma lem3607844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : term11 A) : term137 A s t.
Proof. exact (conj (@lem3607740 A t h1) (@lem3607749 A s t h2)). Qed.
Lemma lem3607846 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) (h1 : term12 A) : term35 A _39092 _39091.
Proof. exact (EQ_MP (@lem3607842 A _39092 _39091) (@lem3607821 A _39091 _39092 h1)). Qed.
Lemma lem3607847 {A : Type'} (_39092 : A -> Prop) (_39091 : A -> Prop) (h1 : term12 A) : term35 A _39092 _39091.
Proof. exact (@lem3607846 A _39092 _39091 h1). Qed.
Lemma lem3607848 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) : term138 A s t.
Proof. exact (@lem3607847 A t (@INTER A s t) h1). Qed.
Lemma lem3607851 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) : term46 A s t.
Proof. exact (@lem3607848 A s t h1 (@lem3607844 A s t h2 h3)). Qed.
Lemma lem3607852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) : term46 A s t.
Proof. exact (@lem3607851 A s t h1 h2 h3). Qed.
Lemma lem3607853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) : term132 A s t.
Proof. exact (fun h0 : term105 A s t => @lem3607852 A s t h1 h2 h3). Qed.
Lemma lem3607855 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607856 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term132 A s t) = (term46 A s t).
Proof. exact (@lem3607855 (term46 A s t)). Qed.
Lemma lem3607857 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) : term46 A s t.
Proof. exact (EQ_MP (@lem3607856 A s t) (@lem3607853 A s t h1 h2 h3)). Qed.
Lemma lem3607860 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3607862 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term133 A s t).
Proof. exact (@lem3607860 (term46 A s t)). Qed.
Lemma lem3607865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term133 A s t.
Proof. exact (EQ_MP (@lem3607862 A s t) (@lem3607587 A s t h1)). Qed.
Lemma lem3607868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (@lem3607865 A s t h4 (@lem3607857 A s t h1 h2 h3)). Qed.
Lemma lem3607869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : term134.
Proof. exact (fun h0 : ~ False => @lem3607868 A s t h1 h2 h3 h4). Qed.
Lemma lem3607871 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3607872 : term134 = False.
Proof. exact (@lem3607871 False). Qed.
Lemma lem3607873 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607872) (@lem3607869 A s t h1 h2 h3 h4)). Qed.
Lemma lem3607874 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A t => @lem3607873 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607593 A t h2)). Qed.
Lemma lem3607875 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607874 A s t h1 h2 h3 h4) (@lem3607593 A t h2)). Qed.
Lemma lem3607876 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem3607733 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607573 A s h2)). Qed.
Lemma lem3607877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607876 A s t h1 h2 h3 h4) (@lem3607573 A s h2)). Qed.
Lemma lem3607878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A t => @lem3607875 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607517 A t h2)). Qed.
Lemma lem3607879 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607878 A s t h1 h2 h3 h4) (@lem3607517 A t h2)). Qed.
Lemma lem3607880 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem3607877 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607441 A s h2)). Qed.
Lemma lem3607881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607880 A s t h1 h2 h3 h4) (@lem3607441 A s h2)). Qed.
Lemma lem3607882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A t) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A t => @lem3607879 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607517 A t h2)). Qed.
Lemma lem3607883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A t) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607882 A s t h1 h2 h3 h4) (@lem3607517 A t h2)). Qed.
Lemma lem3607884 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem3607881 A s t h1 h2 h3 h4) (fun h5 : False => @lem3607441 A s h2)). Qed.
Lemma lem3607885 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : @FINITE A s) (h3 : term11 A) (h4 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607884 A s t h1 h2 h3 h4) (@lem3607441 A s h2)). Qed.
Lemma lem3607886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term44 A s t) : False.
Proof. exact (or_elim (@lem3607361 A s t h3) (fun h0 : @FINITE A s => @lem3607885 A s t h1 h0 h2 h3) (fun h0 : @FINITE A t => @lem3607883 A s t h1 h0 h2 h3)). Qed.
Lemma lem3607887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term44 A s t) : (term44 A s t) = False.
Proof. exact (prop_ext (fun h4 : term44 A s t => @lem3607886 A s t h1 h2 h3) (fun h4 : False => @lem3607359 A s t h3)). Qed.
Lemma lem3607888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607887 A s t h1 h2 h3) (@lem3607359 A s t h3)). Qed.
Lemma lem3607889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term44 A s t) : (term11 A) = False.
Proof. exact (prop_ext (fun h4 : term11 A => @lem3607888 A s t h1 h2 h3) (fun h4 : False => @lem3607337 A h2)). Qed.
Lemma lem3607890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term12 A) (h2 : term11 A) (h3 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3607889 A s t h1 h2 h3) (@lem3607337 A h2)). Qed.
Lemma lem3607891 {A : Type'} (s : A -> Prop) (h1 : term12 A) (h2 : term55 A s) (h3 : term11 A) : False.
Proof. exact (ex_elim (@lem3607274 A s h2) (fun t : A -> Prop => fun h0 : term54 A s t => @lem3607890 A s t h1 h3 h0)). Qed.
Lemma lem3607892 {A : Type'} (h1 : term12 A) (h2 : term10 A) (h3 : term11 A) : False.
Proof. exact (ex_elim (@lem3607081 A h2) (fun s : A -> Prop => fun h0 : term60 A s => @lem3607891 A s h1 h0 h3)). Qed.
Lemma lem3607893 {A : Type'} (h1 : term12 A) (h2 : term10 A) (h3 : term11 A) : (term11 A) = False.
Proof. exact (prop_ext (fun h4 : term11 A => @lem3607892 A h1 h2 h3) (fun h4 : False => @lem3607273 A h3)). Qed.
Lemma lem3607894 {A : Type'} (h1 : term12 A) (h2 : term10 A) (h3 : term11 A) : False.
Proof. exact (EQ_MP (@lem3607893 A h1 h2 h3) (@lem3607273 A h3)). Qed.
Lemma lem3607895 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term17 A.
Proof. exact (fun h0 : term11 A => @lem3607894 A h1 h2 h0). Qed.
Lemma lem3607896 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3607897 {A : Type'} (h1 : term12 A) (h2 : term10 A) : term18 A.
Proof. exact (EQ_MP (@lem3607896 A) (@lem3607895 A h1 h2)). Qed.
Lemma lem3607898 {A : Type'} (h1 : term10 A) : term21 A.
Proof. exact (fun h0 : term12 A => @lem3607897 A h0 h1). Qed.
Lemma lem3607899 {A : Type'} : term23 A.
Proof. exact (fun h0 : term10 A => @lem3607898 A h0). Qed.
Lemma lem3607900 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3606990 A) (@lem3607899 A)). Qed.
Lemma lem3607902 {A : Type'} : term13 A.
Proof. exact (@lem3606806 A (@lem3607900 A)). Qed.
Lemma lem3607903 {A : Type'} (h1 : term10 A) : term20 A.
Proof. exact (@lem3607902 A (@lem3606787 A h1)). Qed.
Lemma lem3607904 {A : Type'} (h1 : term10 A) : term17 A.
Proof. exact (@lem3607903 A h1 (@lem3606789 A)). Qed.
Lemma lem3607905 {A : Type'} (h1 : term10 A) : False.
Proof. exact (@lem3607904 A h1 (@lem3606788 A)). Qed.
Lemma lem3607906 {A : Type'} (h1 : term10 A) : (term10 A) = False.
Proof. exact (prop_ext (fun h2 : term10 A => @lem3607905 A h1) (fun h2 : False => @lem3606787 A h1)). Qed.
Lemma lem3607907 {A : Type'} (h1 : term10 A) : False.
Proof. exact (EQ_MP (@lem3607906 A h1) (@lem3606787 A h1)). Qed.
Lemma lem3607908 {A : Type'} : term9 A.
Proof. exact (fun h0 : term10 A => @lem3607907 A h0). Qed.
Lemma lem3607909 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3606786 A) (@lem3607908 A)). Qed.
