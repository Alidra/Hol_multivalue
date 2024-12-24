Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNION_OF_MONO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm21386_spec.
Lemma lem4842620 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4842621 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4842622 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4842621 A P) (@lem4842620 A P)). Qed.
Lemma lem4842623 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4842622 A P Q). Qed.
Lemma lem4842624 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4842647 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4842624 A P Q) (@lem4842623 A P Q)). Qed.
Lemma lem4842648 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4842647 A P Q). Qed.
Lemma lem4842665 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842666 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = (term4 A P Q s).
Proof. exact (MK_COMB (@lem4842648 A P Q) (@lem4842665 A s)). Qed.
Lemma lem4842668 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4842669 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4842668 (A -> Prop) Prop f y). Qed.
Lemma lem4842670 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term7 A P Q s) = (term4 A P Q s).
Proof. exact (@lem4842669 A (term3 A P Q) s). Qed.
Lemma lem4842671 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (eq_refl (term4 A P Q s)). Qed.
Lemma lem4842672 {A : Type'} (P : type180 A) (Q : type686 A) : (term9 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842671 A P Q s)). Qed.
Lemma lem4842673 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842674 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term7 A P Q s) = (term4 A P Q s).
Proof. exact (MK_COMB (@lem4842672 A P Q) (@lem4842673 A s)). Qed.
Lemma lem4842675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4842676 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term10 A P Q s) = (term11 A P Q s).
Proof. exact (MK_COMB (@lem4842675) (@lem4842674 A P Q s)). Qed.
Lemma lem4842677 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (eq_refl (term4 A P Q s)). Qed.
Lemma lem4842678 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : ((term7 A P Q s) = (term4 A P Q s)) = ((term4 A P Q s) = (term8 A P Q s)).
Proof. exact (MK_COMB (@lem4842676 A P Q s) (@lem4842677 A P Q s)). Qed.
Lemma lem4842679 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term4 A P Q s) = (term8 A P Q s).
Proof. exact (EQ_MP (@lem4842678 A P Q s) (@lem4842670 A P Q s)). Qed.
Lemma lem4842696 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@UNION_OF A P Q s) = (term8 A P Q s).
Proof. exact (TRANS (@lem4842666 A P Q s) (@lem4842679 A P Q s)). Qed.
Lemma lem4842697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842698 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term12 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4842697) (@lem4842696 A P Q s)). Qed.
Lemma lem4842705 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term14 A Q Q').
Proof. exact (eq_refl (term14 A Q Q')). Qed.
Lemma lem4842706 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term15 A P s Q Q') = (term16 A P s Q Q').
Proof. exact (MK_COMB (@lem4842698 A P Q s) (@lem4842705 A Q Q')). Qed.
Lemma lem4842709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4842710 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term17 A P s Q Q') = (term18 A P s Q Q').
Proof. exact (MK_COMB (@lem4842709) (@lem4842706 A P s Q Q')). Qed.
Lemma lem4842712 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4842624 A P Q) (@lem4842623 A P Q)). Qed.
Lemma lem4842713 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4842712 A P Q). Qed.
Lemma lem4842714 {A : Type'} (P : type180 A) (Q' : type686 A) : (@UNION_OF A P Q') = (term3 A P Q').
Proof. exact (@lem4842713 A P Q'). Qed.
Lemma lem4842731 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842732 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (@UNION_OF A P Q' s) = (term4 A P Q' s).
Proof. exact (MK_COMB (@lem4842714 A P Q') (@lem4842731 A s)). Qed.
Lemma lem4842734 {A B : Type'} (f : A -> B) (y : A) : (term5 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4842735 {A : Type'} (f : type686 A) (y : A -> Prop) : (term6 A f y) = (f y).
Proof. exact (@lem4842734 (A -> Prop) Prop f y). Qed.
Lemma lem4842736 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term7 A P Q' s) = (term4 A P Q' s).
Proof. exact (@lem4842735 A (term3 A P Q') s). Qed.
Lemma lem4842737 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (eq_refl (term4 A P Q' s)). Qed.
Lemma lem4842738 {A : Type'} (P : type180 A) (Q' : type686 A) : (term9 A P Q') = (term3 A P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842737 A P Q' s)). Qed.
Lemma lem4842739 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842740 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term7 A P Q' s) = (term4 A P Q' s).
Proof. exact (MK_COMB (@lem4842738 A P Q') (@lem4842739 A s)). Qed.
Lemma lem4842741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4842742 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term10 A P Q' s) = (term11 A P Q' s).
Proof. exact (MK_COMB (@lem4842741) (@lem4842740 A P Q' s)). Qed.
Lemma lem4842743 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (eq_refl (term4 A P Q' s)). Qed.
Lemma lem4842744 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : ((term7 A P Q' s) = (term4 A P Q' s)) = ((term4 A P Q' s) = (term8 A P Q' s)).
Proof. exact (MK_COMB (@lem4842742 A P Q' s) (@lem4842743 A P Q' s)). Qed.
Lemma lem4842745 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term4 A P Q' s) = (term8 A P Q' s).
Proof. exact (EQ_MP (@lem4842744 A P Q' s) (@lem4842736 A P Q' s)). Qed.
Lemma lem4842762 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (@UNION_OF A P Q' s) = (term8 A P Q' s).
Proof. exact (TRANS (@lem4842732 A P Q' s) (@lem4842745 A P Q' s)). Qed.
Lemma lem4842763 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term19 A Q P Q' s) = (term20 A Q P Q' s).
Proof. exact (MK_COMB (@lem4842710 A P s Q Q') (@lem4842762 A P Q' s)). Qed.
Lemma lem4842766 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term21 A Q P Q') = (term22 A Q P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842763 A Q P Q' s)). Qed.
Lemma lem4842767 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842768 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term23 A Q P Q') = (term24 A Q P Q').
Proof. exact (MK_COMB (@lem4842767 A) (@lem4842766 A Q P Q')). Qed.
Lemma lem4842773 {A : Type'} (Q : type686 A) (P : type180 A) : (term25 A Q P) = (term26 A Q P).
Proof. exact (fun_ext (fun Q' : type686 A => @lem4842768 A Q P Q')). Qed.
Lemma lem4842774 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4842775 {A : Type'} (Q : type686 A) (P : type180 A) : (term27 A Q P) = (term28 A Q P).
Proof. exact (MK_COMB (@lem4842774 A) (@lem4842773 A Q P)). Qed.
Lemma lem4842780 {A : Type'} (P : type180 A) : (term29 A P) = (term30 A P).
Proof. exact (fun_ext (fun Q : type686 A => @lem4842775 A Q P)). Qed.
Lemma lem4842781 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4842782 {A : Type'} (P : type180 A) : (term31 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4842781 A) (@lem4842780 A P)). Qed.
Lemma lem4842787 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun P : type180 A => @lem4842782 A P)). Qed.
Lemma lem4842788 {A : Type'} : (@all (((A -> Prop) -> Prop) -> Prop)) = (@all (((A -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((A -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4842789 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4842788 A) (@lem4842787 A)). Qed.
Lemma lem4842794 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem4842789 A)). Qed.
Lemma lem4842796 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4842797 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (@lem4842796 (term36 A)). Qed.
Lemma lem4842798 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (SYM (@lem4842797 A)). Qed.
Lemma lem4842799 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem4842802 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem4842803 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem4842802 A h0). Qed.
Lemma lem4842804 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem4842805 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem4842806 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem4842804 A h2 (@lem4842805 A h1)). Qed.
Lemma lem4842807 {A : Type'} (h1 : term38 A) : term41 A.
Proof. exact (fun h0 : term40 A => @lem4842806 A h1 h0). Qed.
Lemma lem4842808 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem4842809 {A : Type'} (h1 : term38 A) (h2 : term40 A) : term38 A.
Proof. exact (@lem4842807 A h1 (@lem4842808 A h2)). Qed.
Lemma lem4842810 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (fun h0 : term38 A => @lem4842809 A h0 h1). Qed.
Lemma lem4842811 {A : Type'} : term42 A.
Proof. exact (fun h0 : term40 A => @lem4842810 A h0). Qed.
Lemma lem4842814 {A : Type'} : term40 A.
Proof. exact (@lem4842811 A (@lem4842803 A)). Qed.
Lemma lem4842815 {A : Type'} : term40 A.
Proof. exact (@lem4842814 A). Qed.
Lemma lem4842817 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4842818 {A : Type'} : (term38 A) = (term43 A).
Proof. exact (@lem4842817 (term39 A)). Qed.
Lemma lem4842820 (t : Prop) : (term44 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4842821 {A : Type'} : (term43 A) = (term36 A).
Proof. exact (@lem4842820 (term36 A)). Qed.
Lemma lem4842928 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem4842818 A) (@lem4842821 A)). Qed.
Lemma lem4842929 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4842934 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term45 A u Q' c) = (term45 A u Q' c).
Proof. exact (eq_refl (term45 A u Q' c)). Qed.
Lemma lem4842935 {A : Type'} (u : type686 A) (Q' : type686 A) : (term46 A u Q') = (term46 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4842934 A u Q' c)). Qed.
Lemma lem4842936 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842937 {A : Type'} (u : type686 A) (Q' : type686 A) : (term47 A u Q') = (term47 A u Q').
Proof. exact (MK_COMB (@lem4842936 A) (@lem4842935 A u Q')). Qed.
Lemma lem4842938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842939 {A : Type'} (u : type686 A) (Q' : type686 A) : (term48 A u Q') = (term48 A u Q').
Proof. exact (MK_COMB (@lem4842938) (@lem4842937 A u Q')). Qed.
Lemma lem4842940 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q' u s) = (term49 A Q' u s).
Proof. exact (MK_COMB (@lem4842939 A u Q') (@lem4842929 A u s)). Qed.
Lemma lem4842943 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4842944 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q' u s) = (term51 A P Q' u s).
Proof. exact (MK_COMB (@lem4842943 A P u) (@lem4842940 A Q' u s)). Qed.
Lemma lem4842945 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term52 A P Q' s) = (term52 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4842944 A P Q' u s)). Qed.
Lemma lem4842946 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4842947 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term8 A P Q' s) = (term8 A P Q' s).
Proof. exact (MK_COMB (@lem4842946 A) (@lem4842945 A P Q' s)). Qed.
Lemma lem4842952 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term53 A Q Q' x) = (term53 A Q Q' x).
Proof. exact (eq_refl (term53 A Q Q' x)). Qed.
Lemma lem4842953 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term54 A Q Q') = (term54 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4842952 A Q Q' x)). Qed.
Lemma lem4842954 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842955 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term14 A Q Q').
Proof. exact (MK_COMB (@lem4842954 A) (@lem4842953 A Q Q')). Qed.
Lemma lem4842956 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4842961 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term45 A u Q c) = (term45 A u Q c).
Proof. exact (eq_refl (term45 A u Q c)). Qed.
Lemma lem4842962 {A : Type'} (u : type686 A) (Q : type686 A) : (term46 A u Q) = (term46 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4842961 A u Q c)). Qed.
Lemma lem4842963 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842964 {A : Type'} (u : type686 A) (Q : type686 A) : (term47 A u Q) = (term47 A u Q).
Proof. exact (MK_COMB (@lem4842963 A) (@lem4842962 A u Q)). Qed.
Lemma lem4842965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842966 {A : Type'} (u : type686 A) (Q : type686 A) : (term48 A u Q) = (term48 A u Q).
Proof. exact (MK_COMB (@lem4842965) (@lem4842964 A u Q)). Qed.
Lemma lem4842967 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q u s) = (term49 A Q u s).
Proof. exact (MK_COMB (@lem4842966 A u Q) (@lem4842956 A u s)). Qed.
Lemma lem4842970 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4842971 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q u s) = (term51 A P Q u s).
Proof. exact (MK_COMB (@lem4842970 A P u) (@lem4842967 A Q u s)). Qed.
Lemma lem4842972 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term52 A P Q s) = (term52 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4842971 A P Q u s)). Qed.
Lemma lem4842973 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4842974 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term8 A P Q s).
Proof. exact (MK_COMB (@lem4842973 A) (@lem4842972 A P Q s)). Qed.
Lemma lem4842975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842976 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term13 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4842975) (@lem4842974 A P Q s)). Qed.
Lemma lem4842977 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term16 A P s Q Q').
Proof. exact (MK_COMB (@lem4842976 A P Q s) (@lem4842955 A Q Q')). Qed.
Lemma lem4842978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4842979 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term18 A P s Q Q') = (term18 A P s Q Q').
Proof. exact (MK_COMB (@lem4842978) (@lem4842977 A P s Q Q')). Qed.
Lemma lem4842980 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term20 A Q P Q' s) = (term20 A Q P Q' s).
Proof. exact (MK_COMB (@lem4842979 A P s Q Q') (@lem4842947 A P Q' s)). Qed.
Lemma lem4842981 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term22 A Q P Q') = (term22 A Q P Q').
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842980 A Q P Q' s)). Qed.
Lemma lem4842982 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842983 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : (term24 A Q P Q') = (term24 A Q P Q').
Proof. exact (MK_COMB (@lem4842982 A) (@lem4842981 A Q P Q')). Qed.
Lemma lem4842984 {A : Type'} (Q : type686 A) (P : type180 A) : (term26 A Q P) = (term26 A Q P).
Proof. exact (fun_ext (fun Q' : type686 A => @lem4842983 A Q P Q')). Qed.
Lemma lem4842985 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4842986 {A : Type'} (Q : type686 A) (P : type180 A) : (term28 A Q P) = (term28 A Q P).
Proof. exact (MK_COMB (@lem4842985 A) (@lem4842984 A Q P)). Qed.
Lemma lem4842987 {A : Type'} (P : type180 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun Q : type686 A => @lem4842986 A Q P)). Qed.
Lemma lem4842988 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4842989 {A : Type'} (P : type180 A) : (term32 A P) = (term32 A P).
Proof. exact (MK_COMB (@lem4842988 A) (@lem4842987 A P)). Qed.
Lemma lem4842990 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (fun_ext (fun P : type180 A => @lem4842989 A P)). Qed.
Lemma lem4842991 {A : Type'} : (@all (((A -> Prop) -> Prop) -> Prop)) = (@all (((A -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((A -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4842992 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (MK_COMB (@lem4842991 A) (@lem4842990 A)). Qed.
Lemma lem4843067 {A : Type'} : (term38 A) = (term36 A).
Proof. exact (TRANS (@lem4842928 A) (@lem4842992 A)). Qed.
Lemma lem4843068 {A : Type'} : (term36 A) = (term38 A).
Proof. exact (SYM (@lem4843067 A)). Qed.
Lemma lem4843069 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term16 A P s Q Q'.
Proof. exact (h1). Qed.
Lemma lem4843071 (p : Prop) : p = (term37 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4843072 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term8 A P Q' s) = (term55 A P Q' s).
Proof. exact (@lem4843071 (term8 A P Q' s)). Qed.
Lemma lem4843073 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term55 A P Q' s) = (term8 A P Q' s).
Proof. exact (SYM (@lem4843072 A P Q' s)). Qed.
Lemma lem4843074 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (h1 : term56 A P Q' s) : term56 A P Q' s.
Proof. exact (h1). Qed.
Lemma lem4843082 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term45 A u Q c) = (term57 A u Q c).
Proof. exact (@lem17265 (@IN (A -> Prop) c u) (Q c)). Qed.
Lemma lem4843083 {A : Type'} (u : type686 A) (Q : type686 A) : (term46 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843082 A u Q c)). Qed.
Lemma lem4843084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843085 {A : Type'} (u : type686 A) (Q : type686 A) : (term47 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4843084 A) (@lem4843083 A u Q)). Qed.
Lemma lem4843086 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4843087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843088 {A : Type'} (u : type686 A) (Q : type686 A) : (term48 A u Q) = (term60 A u Q).
Proof. exact (MK_COMB (@lem4843087) (@lem4843085 A u Q)). Qed.
Lemma lem4843089 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term49 A Q u s) = (term61 A Q u s).
Proof. exact (MK_COMB (@lem4843088 A u Q) (@lem4843086 A u s)). Qed.
Lemma lem4843091 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4843092 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term51 A P Q u s) = (term62 A P Q u s).
Proof. exact (MK_COMB (@lem4843091 A P u) (@lem4843089 A Q u s)). Qed.
Lemma lem4843093 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term52 A P Q s) = (term63 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843092 A P Q u s)). Qed.
Lemma lem4843094 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4843095 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term8 A P Q s) = (term64 A P Q s).
Proof. exact (MK_COMB (@lem4843094 A) (@lem4843093 A P Q s)). Qed.
Lemma lem4843102 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term53 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (@lem17265 (Q x) (Q' x)). Qed.
Lemma lem4843103 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term54 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4843102 A Q Q' x)). Qed.
Lemma lem4843104 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843105 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term14 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4843104 A) (@lem4843103 A Q Q')). Qed.
Lemma lem4843106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843107 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term13 A P Q s) = (term68 A P Q s).
Proof. exact (MK_COMB (@lem4843106) (@lem4843095 A P Q s)). Qed.
Lemma lem4843108 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term69 A P s Q Q').
Proof. exact (MK_COMB (@lem4843107 A P Q s) (@lem4843105 A Q Q')). Qed.
Lemma lem4843203 {A : Type'} (P : A -> Prop) (Q : Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4843204 {A : Type'} (P : type180 A) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (@lem4843203 (type686 A) P Q). Qed.
Lemma lem4843205 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term74 A P s Q Q') = (term75 A P s Q Q').
Proof. exact (@lem4843204 A (term63 A P Q s) (term67 A Q Q')). Qed.
Lemma lem4843206 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term76 A P Q s u) = (term62 A P Q u s).
Proof. exact (eq_refl (term76 A P Q s u)). Qed.
Lemma lem4843207 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term77 A P Q s) = (term63 A P Q s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843206 A P Q u s)). Qed.
Lemma lem4843208 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4843209 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term78 A P Q s) = (term64 A P Q s).
Proof. exact (MK_COMB (@lem4843208 A) (@lem4843207 A P Q s)). Qed.
Lemma lem4843210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843211 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term79 A P Q s) = (term68 A P Q s).
Proof. exact (MK_COMB (@lem4843210) (@lem4843209 A P Q s)). Qed.
Lemma lem4843212 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (eq_refl (term67 A Q Q')). Qed.
Lemma lem4843213 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term74 A P s Q Q') = (term69 A P s Q Q').
Proof. exact (MK_COMB (@lem4843211 A P Q s) (@lem4843212 A Q Q')). Qed.
Lemma lem4843214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843215 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term80 A P s Q Q') = (term81 A P s Q Q').
Proof. exact (MK_COMB (@lem4843214) (@lem4843213 A P s Q Q')). Qed.
Lemma lem4843216 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term76 A P Q s u) = (term62 A P Q u s).
Proof. exact (eq_refl (term76 A P Q s u)). Qed.
Lemma lem4843217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843218 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term82 A P Q s u) = (term83 A P Q u s).
Proof. exact (MK_COMB (@lem4843217) (@lem4843216 A P Q u s)). Qed.
Lemma lem4843219 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (eq_refl (term67 A Q Q')). Qed.
Lemma lem4843220 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term84 A P s u Q Q') = (term85 A P u s Q Q').
Proof. exact (MK_COMB (@lem4843218 A P Q u s) (@lem4843219 A Q Q')). Qed.
Lemma lem4843221 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term86 A P s Q Q') = (term87 A P s Q Q').
Proof. exact (fun_ext (fun u : type686 A => @lem4843220 A P u s Q Q')). Qed.
Lemma lem4843222 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4843223 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term75 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (MK_COMB (@lem4843222 A) (@lem4843221 A P s Q Q')). Qed.
Lemma lem4843224 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : ((term74 A P s Q Q') = (term75 A P s Q Q')) = ((term69 A P s Q Q') = (term88 A P s Q Q')).
Proof. exact (MK_COMB (@lem4843215 A P s Q Q') (@lem4843223 A P s Q Q')). Qed.
Lemma lem4843226 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term69 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (EQ_MP (@lem4843224 A P s Q Q') (@lem4843205 A P s Q Q')). Qed.
Lemma lem4843227 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term16 A P s Q Q') = (term88 A P s Q Q').
Proof. exact (TRANS (@lem4843108 A P s Q Q') (@lem4843226 A P s Q Q')). Qed.
Lemma lem4843228 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term88 A P s Q Q'.
Proof. exact (EQ_MP (@lem4843227 A P s Q Q') (@lem4843069 A P s Q Q' h1)). Qed.
Lemma lem4843236 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term89 A u Q' c) = (term90 A u Q' c).
Proof. exact (@lem17362 (@IN (A -> Prop) c u) (Q' c)). Qed.
Lemma lem4843237 {A : Type'} (P : type686 A) : (term91 A P) = (term92 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4843238 {A : Type'} (u : type686 A) (Q' : type686 A) : (term93 A u Q') = (term94 A u Q').
Proof. exact (@lem4843237 A (term46 A u Q')). Qed.
Lemma lem4843239 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term95 A u Q' c) = (term45 A u Q' c).
Proof. exact (eq_refl (term95 A u Q' c)). Qed.
Lemma lem4843240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4843241 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term96 A u Q' c) = (term89 A u Q' c).
Proof. exact (MK_COMB (@lem4843240) (@lem4843239 A u Q' c)). Qed.
Lemma lem4843242 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term96 A u Q' c) = (term90 A u Q' c).
Proof. exact (TRANS (@lem4843241 A u Q' c) (@lem4843236 A u Q' c)). Qed.
Lemma lem4843243 {A : Type'} (u : type686 A) (Q' : type686 A) : (term97 A u Q') = (term98 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843242 A u Q' c)). Qed.
Lemma lem4843244 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843245 {A : Type'} (u : type686 A) (Q' : type686 A) : (term94 A u Q') = (term99 A u Q').
Proof. exact (MK_COMB (@lem4843244 A) (@lem4843243 A u Q')). Qed.
Lemma lem4843246 {A : Type'} (u : type686 A) (Q' : type686 A) : (term93 A u Q') = (term99 A u Q').
Proof. exact (TRANS (@lem4843238 A u Q') (@lem4843245 A u Q')). Qed.
Lemma lem4843247 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4843248 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4843249 {A : Type'} (u : type686 A) (Q' : type686 A) : (term101 A u Q') = (term102 A u Q').
Proof. exact (MK_COMB (@lem4843248) (@lem4843246 A u Q')). Qed.
Lemma lem4843250 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term103 A Q' u s) = (term104 A Q' u s).
Proof. exact (MK_COMB (@lem4843249 A u Q') (@lem4843247 A u s)). Qed.
Lemma lem4843251 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term105 A Q' u s) = (term103 A Q' u s).
Proof. exact (@lem17045 (term47 A u Q') ((@UNIONS A u) = s)). Qed.
Lemma lem4843252 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term105 A Q' u s) = (term104 A Q' u s).
Proof. exact (TRANS (@lem4843251 A Q' u s) (@lem4843250 A Q' u s)). Qed.
Lemma lem4843254 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4843255 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term107 A P Q' u s) = (term108 A P Q' u s).
Proof. exact (MK_COMB (@lem4843254 A P u) (@lem4843252 A Q' u s)). Qed.
Lemma lem4843256 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term109 A P Q' u s) = (term107 A P Q' u s).
Proof. exact (@lem17045 (P u) (term49 A Q' u s)). Qed.
Lemma lem4843257 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term109 A P Q' u s) = (term108 A P Q' u s).
Proof. exact (TRANS (@lem4843256 A P Q' u s) (@lem4843255 A P Q' u s)). Qed.
Lemma lem4843258 {A : Type'} (P : type180 A) : (term110 A P) = (term111 A P).
Proof. exact (@lem18394 (type686 A) P). Qed.
Lemma lem4843259 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term112 A P Q' s).
Proof. exact (@lem4843258 A (term52 A P Q' s)). Qed.
Lemma lem4843260 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term113 A P Q' s u) = (term51 A P Q' u s).
Proof. exact (eq_refl (term113 A P Q' s u)). Qed.
Lemma lem4843261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4843262 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term114 A P Q' s u) = (term109 A P Q' u s).
Proof. exact (MK_COMB (@lem4843261) (@lem4843260 A P Q' u s)). Qed.
Lemma lem4843263 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term114 A P Q' s u) = (term108 A P Q' u s).
Proof. exact (TRANS (@lem4843262 A P Q' u s) (@lem4843257 A P Q' u s)). Qed.
Lemma lem4843264 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term115 A P Q' s) = (term116 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843263 A P Q' u s)). Qed.
Lemma lem4843265 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843266 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term112 A P Q' s) = (term117 A P Q' s).
Proof. exact (MK_COMB (@lem4843265 A) (@lem4843264 A P Q' s)). Qed.
Lemma lem4843267 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term117 A P Q' s).
Proof. exact (TRANS (@lem4843259 A P Q' s) (@lem4843266 A P Q' s)). Qed.
Lemma lem4843366 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4843367 {A : Type'} (P : type686 A) (Q : Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (@lem4843366 (A -> Prop) P Q). Qed.
Lemma lem4843368 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term122 A Q' u s) = (term123 A Q' u s).
Proof. exact (@lem4843367 A (term98 A u Q') (term100 A u s)). Qed.
Lemma lem4843369 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term124 A u Q' c) = (term90 A u Q' c).
Proof. exact (eq_refl (term124 A u Q' c)). Qed.
Lemma lem4843370 {A : Type'} (u : type686 A) (Q' : type686 A) : (term125 A u Q') = (term98 A u Q').
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843369 A u Q' c)). Qed.
Lemma lem4843371 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843372 {A : Type'} (u : type686 A) (Q' : type686 A) : (term126 A u Q') = (term99 A u Q').
Proof. exact (MK_COMB (@lem4843371 A) (@lem4843370 A u Q')). Qed.
Lemma lem4843373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4843374 {A : Type'} (u : type686 A) (Q' : type686 A) : (term127 A u Q') = (term102 A u Q').
Proof. exact (MK_COMB (@lem4843373) (@lem4843372 A u Q')). Qed.
Lemma lem4843375 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4843376 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term122 A Q' u s) = (term104 A Q' u s).
Proof. exact (MK_COMB (@lem4843374 A u Q') (@lem4843375 A u s)). Qed.
Lemma lem4843377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843378 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term128 A Q' u s) = (term129 A Q' u s).
Proof. exact (MK_COMB (@lem4843377) (@lem4843376 A Q' u s)). Qed.
Lemma lem4843379 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term124 A u Q' c) = (term90 A u Q' c).
Proof. exact (eq_refl (term124 A u Q' c)). Qed.
Lemma lem4843380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4843381 {A : Type'} (u : type686 A) (Q' : type686 A) (c : A -> Prop) : (term130 A u Q' c) = (term131 A u Q' c).
Proof. exact (MK_COMB (@lem4843380) (@lem4843379 A u Q' c)). Qed.
Lemma lem4843382 {A : Type'} (u : type686 A) (s : A -> Prop) : (term100 A u s) = (term100 A u s).
Proof. exact (eq_refl (term100 A u s)). Qed.
Lemma lem4843383 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term132 A Q' c u s) = (term133 A Q' c u s).
Proof. exact (MK_COMB (@lem4843381 A u Q' c) (@lem4843382 A u s)). Qed.
Lemma lem4843384 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term134 A Q' u s) = (term135 A Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843383 A Q' c u s)). Qed.
Lemma lem4843385 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843386 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term123 A Q' u s) = (term136 A Q' u s).
Proof. exact (MK_COMB (@lem4843385 A) (@lem4843384 A Q' u s)). Qed.
Lemma lem4843387 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : ((term122 A Q' u s) = (term123 A Q' u s)) = ((term104 A Q' u s) = (term136 A Q' u s)).
Proof. exact (MK_COMB (@lem4843378 A Q' u s) (@lem4843386 A Q' u s)). Qed.
Lemma lem4843388 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term104 A Q' u s) = (term136 A Q' u s).
Proof. exact (EQ_MP (@lem4843387 A Q' u s) (@lem4843368 A Q' u s)). Qed.
Lemma lem4843389 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4843390 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term108 A P Q' u s) = (term137 A P Q' u s).
Proof. exact (MK_COMB (@lem4843389 A P u) (@lem4843388 A Q' u s)). Qed.
Lemma lem4843392 {A : Type'} (P : Prop) (Q : A -> Prop) : (term138 A P Q) = (term139 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4843393 {A : Type'} (P : Prop) (Q : type686 A) : (term140 A P Q) = (term141 A P Q).
Proof. exact (@lem4843392 (A -> Prop) P Q). Qed.
Lemma lem4843394 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term142 A P Q' u s) = (term143 A P Q' u s).
Proof. exact (@lem4843393 A (term144 A P u) (term135 A Q' u s)). Qed.
Lemma lem4843395 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term145 A Q' u s c) = (term133 A Q' c u s).
Proof. exact (eq_refl (term145 A Q' u s c)). Qed.
Lemma lem4843396 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term146 A Q' u s) = (term135 A Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843395 A Q' c u s)). Qed.
Lemma lem4843397 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843398 {A : Type'} (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term147 A Q' u s) = (term136 A Q' u s).
Proof. exact (MK_COMB (@lem4843397 A) (@lem4843396 A Q' u s)). Qed.
Lemma lem4843399 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4843400 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term142 A P Q' u s) = (term137 A P Q' u s).
Proof. exact (MK_COMB (@lem4843399 A P u) (@lem4843398 A Q' u s)). Qed.
Lemma lem4843401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843402 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term148 A P Q' u s) = (term149 A P Q' u s).
Proof. exact (MK_COMB (@lem4843401) (@lem4843400 A P Q' u s)). Qed.
Lemma lem4843403 {A : Type'} (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term145 A Q' u s c) = (term133 A Q' c u s).
Proof. exact (eq_refl (term145 A Q' u s c)). Qed.
Lemma lem4843404 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4843405 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term150 A P Q' u s c) = (term151 A P Q' c u s).
Proof. exact (MK_COMB (@lem4843404 A P u) (@lem4843403 A Q' c u s)). Qed.
Lemma lem4843406 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term152 A P Q' u s) = (term153 A P Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843405 A P Q' c u s)). Qed.
Lemma lem4843407 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843408 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term143 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (MK_COMB (@lem4843407 A) (@lem4843406 A P Q' u s)). Qed.
Lemma lem4843409 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : ((term142 A P Q' u s) = (term143 A P Q' u s)) = ((term137 A P Q' u s) = (term154 A P Q' u s)).
Proof. exact (MK_COMB (@lem4843402 A P Q' u s) (@lem4843408 A P Q' u s)). Qed.
Lemma lem4843410 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term137 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (EQ_MP (@lem4843409 A P Q' u s) (@lem4843394 A P Q' u s)). Qed.
Lemma lem4843411 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term108 A P Q' u s) = (term154 A P Q' u s).
Proof. exact (TRANS (@lem4843390 A P Q' u s) (@lem4843410 A P Q' u s)). Qed.
Lemma lem4843412 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term116 A P Q' s) = (term155 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843411 A P Q' u s)). Qed.
Lemma lem4843413 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843414 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term117 A P Q' s) = (term156 A P Q' s).
Proof. exact (MK_COMB (@lem4843413 A) (@lem4843412 A P Q' s)). Qed.
Lemma lem4843416 {A B : Type'} (P : type1413 A B) : (term157 A B P) = (term158 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4843417 {A : Type'} (P : type174 A) : (term159 A P) = (term160 A P).
Proof. exact (@lem4843416 (type686 A) (A -> Prop) P). Qed.
Lemma lem4843418 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term161 A P Q' s) = (term162 A P Q' s).
Proof. exact (@lem4843417 A (term163 A P Q' s)). Qed.
Lemma lem4843419 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term164 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (eq_refl (term164 A P Q' s u)). Qed.
Lemma lem4843420 {A : Type'} (c : A -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4843421 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) (c : A -> Prop) : (term165 A P Q' s u c) = (term166 A P Q' u s c).
Proof. exact (MK_COMB (@lem4843419 A P Q' u s) (@lem4843420 A c)). Qed.
Lemma lem4843422 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term166 A P Q' u s c) = (term151 A P Q' c u s).
Proof. exact (eq_refl (term166 A P Q' u s c)). Qed.
Lemma lem4843423 {A : Type'} (P : type180 A) (Q' : type686 A) (c : A -> Prop) (u : type686 A) (s : A -> Prop) : (term165 A P Q' s u c) = (term151 A P Q' c u s).
Proof. exact (TRANS (@lem4843421 A P Q' u s c) (@lem4843422 A P Q' c u s)). Qed.
Lemma lem4843424 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term167 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843423 A P Q' c u s)). Qed.
Lemma lem4843425 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4843426 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term168 A P Q' s u) = (term154 A P Q' u s).
Proof. exact (MK_COMB (@lem4843425 A) (@lem4843424 A P Q' u s)). Qed.
Lemma lem4843427 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term169 A P Q' s) = (term155 A P Q' s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843426 A P Q' u s)). Qed.
Lemma lem4843428 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843429 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term161 A P Q' s) = (term156 A P Q' s).
Proof. exact (MK_COMB (@lem4843428 A) (@lem4843427 A P Q' s)). Qed.
Lemma lem4843430 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843431 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term170 A P Q' s) = (term171 A P Q' s).
Proof. exact (MK_COMB (@lem4843430) (@lem4843429 A P Q' s)). Qed.
Lemma lem4843432 {A : Type'} (P : type180 A) (Q' : type686 A) (u : type686 A) (s : A -> Prop) : (term164 A P Q' s u) = (term153 A P Q' u s).
Proof. exact (eq_refl (term164 A P Q' s u)). Qed.
Lemma lem4843433 {A : Type'} (c : type178 A) (u : type686 A) : (c u) = (c u).
Proof. exact (eq_refl (c u)). Qed.
Lemma lem4843434 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (c : type178 A) (u : type686 A) : (term172 A P Q' s c u) = (term173 A P Q' s c u).
Proof. exact (MK_COMB (@lem4843432 A P Q' u s) (@lem4843433 A c u)). Qed.
Lemma lem4843435 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term173 A P Q' s c u) = (term174 A P Q' c u s).
Proof. exact (eq_refl (term173 A P Q' s c u)). Qed.
Lemma lem4843436 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term172 A P Q' s c u) = (term174 A P Q' c u s).
Proof. exact (TRANS (@lem4843434 A P Q' s c u) (@lem4843435 A P Q' c u s)). Qed.
Lemma lem4843437 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term175 A P Q' s c) = (term176 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843436 A P Q' c u s)). Qed.
Lemma lem4843438 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843439 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term177 A P Q' s c) = (term178 A P Q' c s).
Proof. exact (MK_COMB (@lem4843438 A) (@lem4843437 A P Q' c s)). Qed.
Lemma lem4843440 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term179 A P Q' s) = (term180 A P Q' s).
Proof. exact (fun_ext (fun c : type178 A => @lem4843439 A P Q' c s)). Qed.
Lemma lem4843441 {A : Type'} : (@ex (((A -> Prop) -> Prop) -> A -> Prop)) = (@ex (((A -> Prop) -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex (((A -> Prop) -> Prop) -> A -> Prop))). Qed.
Lemma lem4843442 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term162 A P Q' s) = (term181 A P Q' s).
Proof. exact (MK_COMB (@lem4843441 A) (@lem4843440 A P Q' s)). Qed.
Lemma lem4843443 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : ((term161 A P Q' s) = (term162 A P Q' s)) = ((term156 A P Q' s) = (term181 A P Q' s)).
Proof. exact (MK_COMB (@lem4843431 A P Q' s) (@lem4843442 A P Q' s)). Qed.
Lemma lem4843444 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term156 A P Q' s) = (term181 A P Q' s).
Proof. exact (EQ_MP (@lem4843443 A P Q' s) (@lem4843418 A P Q' s)). Qed.
Lemma lem4843446 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term117 A P Q' s) = (term181 A P Q' s).
Proof. exact (TRANS (@lem4843414 A P Q' s) (@lem4843444 A P Q' s)). Qed.
Lemma lem4843447 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) : (term56 A P Q' s) = (term181 A P Q' s).
Proof. exact (TRANS (@lem4843267 A P Q' s) (@lem4843446 A P Q' s)). Qed.
Lemma lem4843448 {A : Type'} (P : type180 A) (Q' : type686 A) (s : A -> Prop) (h1 : term56 A P Q' s) : term181 A P Q' s.
Proof. exact (EQ_MP (@lem4843447 A P Q' s) (@lem4843074 A P Q' s h1)). Qed.
Lemma lem4843449 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term178 A P Q' c s.
Proof. exact (h1). Qed.
Lemma lem4843450 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term85 A P u s Q Q'.
Proof. exact (h1). Qed.
Lemma lem4843487 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term174 A P Q' c u s).
Proof. exact (eq_refl (term174 A P Q' c u s)). Qed.
Lemma lem4843488 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term176 A P Q' c s) = (term176 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843487 A P Q' c u s)). Qed.
Lemma lem4843489 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843490 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term178 A P Q' c s) = (term178 A P Q' c s).
Proof. exact (MK_COMB (@lem4843489 A) (@lem4843488 A P Q' c s)). Qed.
Lemma lem4843491 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term178 A P Q' c s.
Proof. exact (EQ_MP (@lem4843490 A P Q' c s) (@lem4843449 A P Q' c s h1)). Qed.
Lemma lem4843502 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term65 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (eq_refl (term65 A Q Q' x)). Qed.
Lemma lem4843503 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term66 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4843502 A Q Q' x)). Qed.
Lemma lem4843504 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843505 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4843504 A) (@lem4843503 A Q Q')). Qed.
Lemma lem4843512 {A : Type'} (u : type686 A) (s : A -> Prop) : ((@UNIONS A u) = s) = ((@UNIONS A u) = s).
Proof. exact (eq_refl ((@UNIONS A u) = s)). Qed.
Lemma lem4843525 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term57 A u Q c) = (term57 A u Q c).
Proof. exact (eq_refl (term57 A u Q c)). Qed.
Lemma lem4843526 {A : Type'} (u : type686 A) (Q : type686 A) : (term58 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843525 A u Q c)). Qed.
Lemma lem4843527 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843528 {A : Type'} (u : type686 A) (Q : type686 A) : (term59 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4843527 A) (@lem4843526 A u Q)). Qed.
Lemma lem4843529 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843530 {A : Type'} (u : type686 A) (Q : type686 A) : (term60 A u Q) = (term60 A u Q).
Proof. exact (MK_COMB (@lem4843529) (@lem4843528 A u Q)). Qed.
Lemma lem4843531 {A : Type'} (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term61 A Q u s) = (term61 A Q u s).
Proof. exact (MK_COMB (@lem4843530 A u Q) (@lem4843512 A u s)). Qed.
Lemma lem4843536 {A : Type'} (P : type180 A) (u : type686 A) : (term50 A P u) = (term50 A P u).
Proof. exact (eq_refl (term50 A P u)). Qed.
Lemma lem4843537 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term62 A P Q u s) = (term62 A P Q u s).
Proof. exact (MK_COMB (@lem4843536 A P u) (@lem4843531 A Q u s)). Qed.
Lemma lem4843538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843539 {A : Type'} (P : type180 A) (Q : type686 A) (u : type686 A) (s : A -> Prop) : (term83 A P Q u s) = (term83 A P Q u s).
Proof. exact (MK_COMB (@lem4843538) (@lem4843537 A P Q u s)). Qed.
Lemma lem4843540 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) : (term85 A P u s Q Q') = (term85 A P u s Q Q').
Proof. exact (MK_COMB (@lem4843539 A P Q u s) (@lem4843505 A Q Q')). Qed.
Lemma lem4843541 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term85 A P u s Q Q'.
Proof. exact (EQ_MP (@lem4843540 A P u s Q Q') (@lem4843450 A P u s Q Q' h1)). Qed.
Lemma lem4843542 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term67 A Q Q'.
Proof. exact (proj2 (@lem4843541 A P u s Q Q' h1)). Qed.
Lemma lem4843543 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term62 A P Q u s.
Proof. exact (proj1 (@lem4843541 A P u s Q Q' h1)). Qed.
Lemma lem4843544 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term61 A Q u s.
Proof. exact (proj2 (@lem4843543 A P u s Q Q' h1)). Qed.
Lemma lem4843547 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term59 A u Q.
Proof. exact (proj1 (@lem4843544 A P u s Q Q' h1)). Qed.
Lemma lem4843565 {A : Type'} (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term182 A Q' c u s) = (term183 A Q' c u s).
Proof. exact (@lem19699 (term184 A c u) (term185 A Q' c u) (term100 A u s)). Qed.
Lemma lem4843568 {A : Type'} (P : type180 A) (u : type686 A) : (term106 A P u) = (term106 A P u).
Proof. exact (eq_refl (term106 A P u)). Qed.
Lemma lem4843569 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term186 A P Q' c u s).
Proof. exact (MK_COMB (@lem4843568 A P u) (@lem4843565 A Q' c u s)). Qed.
Lemma lem4843576 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term186 A P Q' c u s) = (term187 A P Q' c u s).
Proof. exact (@lem19490 (term188 A c u s) (term144 A P u) (term189 A Q' c u s)). Qed.
Lemma lem4843577 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (u : type686 A) (s : A -> Prop) : (term174 A P Q' c u s) = (term187 A P Q' c u s).
Proof. exact (TRANS (@lem4843569 A P Q' c u s) (@lem4843576 A P Q' c u s)). Qed.
Lemma lem4843578 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term176 A P Q' c s) = (term190 A P Q' c s).
Proof. exact (fun_ext (fun u : type686 A => @lem4843577 A P Q' c u s)). Qed.
Lemma lem4843579 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4843581 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) : (term178 A P Q' c s) = (term191 A P Q' c s).
Proof. exact (MK_COMB (@lem4843579 A) (@lem4843578 A P Q' c s)). Qed.
Lemma lem4843582 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term191 A P Q' c s.
Proof. exact (EQ_MP (@lem4843581 A P Q' c s) (@lem4843491 A P Q' c s h1)). Qed.
Lemma lem4843590 {A : Type'} (Q : type686 A) (Q' : type686 A) (x : A -> Prop) : (term65 A Q Q' x) = (term65 A Q Q' x).
Proof. exact (eq_refl (term65 A Q Q' x)). Qed.
Lemma lem4843591 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term66 A Q Q') = (term66 A Q Q').
Proof. exact (fun_ext (fun x : A -> Prop => @lem4843590 A Q Q' x)). Qed.
Lemma lem4843592 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843594 {A : Type'} (Q : type686 A) (Q' : type686 A) : (term67 A Q Q') = (term67 A Q Q').
Proof. exact (MK_COMB (@lem4843592 A) (@lem4843591 A Q Q')). Qed.
Lemma lem4843595 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term67 A Q Q'.
Proof. exact (EQ_MP (@lem4843594 A Q Q') (@lem4843542 A P u s Q Q' h1)). Qed.
Lemma lem4843607 {A : Type'} (u : type686 A) (Q : type686 A) (c : A -> Prop) : (term57 A u Q c) = (term57 A u Q c).
Proof. exact (eq_refl (term57 A u Q c)). Qed.
Lemma lem4843608 {A : Type'} (u : type686 A) (Q : type686 A) : (term58 A u Q) = (term58 A u Q).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4843607 A u Q c)). Qed.
Lemma lem4843609 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4843611 {A : Type'} (u : type686 A) (Q : type686 A) : (term59 A u Q) = (term59 A u Q).
Proof. exact (MK_COMB (@lem4843609 A) (@lem4843608 A u Q)). Qed.
Lemma lem4843612 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term59 A u Q.
Proof. exact (EQ_MP (@lem4843611 A u Q) (@lem4843547 A P u s Q Q' h1)). Qed.
Lemma lem4843617 {A : Type'} (_60056 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term192 A P Q' c s _60056.
Proof. exact (@lem4843582 A P Q' c s h1 _60056). Qed.
Lemma lem4843618 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term192 A P Q' c s _60056) = (term187 A P Q' c _60056 s).
Proof. exact (eq_refl (term192 A P Q' c s _60056)). Qed.
Lemma lem4843619 {A : Type'} (_60056 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term187 A P Q' c _60056 s.
Proof. exact (EQ_MP (@lem4843618 A P Q' c _60056 s) (@lem4843617 A _60056 P Q' c s h1)). Qed.
Lemma lem4843620 {A : Type'} (_60057 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term193 A Q Q' _60057.
Proof. exact (@lem4843595 A P u s Q Q' h1 _60057). Qed.
Lemma lem4843621 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60057 : A -> Prop) : (term193 A Q Q' _60057) = (term65 A Q Q' _60057).
Proof. exact (eq_refl (term193 A Q Q' _60057)). Qed.
Lemma lem4843623 {A : Type'} (_60058 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term194 A u Q _60058.
Proof. exact (@lem4843612 A P u s Q Q' h1 _60058). Qed.
Lemma lem4843624 {A : Type'} (u : type686 A) (Q : type686 A) (_60058 : A -> Prop) : (term194 A u Q _60058) = (term57 A u Q _60058).
Proof. exact (eq_refl (term194 A u Q _60058)). Qed.
Lemma lem4843643 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (@UNIONS A u) = s.
Proof. exact (proj2 (@lem4843544 A P u s Q Q' h1)). Qed.
Lemma lem4843653 {A : Type'} (_60056 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term195 A P c _60056 s.
Proof. exact (proj1 (@lem4843619 A _60056 P Q' c s h1)). Qed.
Lemma lem4843663 {A : Type'} (_60056 : type686 A) (P : type180 A) (Q' : type686 A) (c : type178 A) (s : A -> Prop) (h1 : term178 A P Q' c s) : term196 A P Q' c _60056 s.
Proof. exact (proj2 (@lem4843619 A _60056 P Q' c s h1)). Qed.
Lemma lem4843664 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : s = (@UNIONS A u).
Proof. exact (SYM (@lem4843643 A P u s Q Q' h1)). Qed.
Lemma lem4843692 {A : Type'} (_60057 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term65 A Q Q' _60057.
Proof. exact (EQ_MP (@lem4843621 A Q Q' _60057) (@lem4843620 A _60057 P u s Q Q' h1)). Qed.
Lemma lem4843720 {A : Type'} (_60058 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term57 A u Q _60058.
Proof. exact (EQ_MP (@lem4843624 A u Q _60058) (@lem4843623 A _60058 P u s Q Q' h1)). Qed.
Lemma lem4843721 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) : (term197 A P c _60056) = (term197 A P c _60056).
Proof. exact (eq_refl (term197 A P c _60056)). Qed.
Lemma lem4843722 {A : Type'} (c : type178 A) (_60056 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term198 A P c _60056 s) = (term199 A P c _60056 u).
Proof. exact (MK_COMB (@lem4843721 A P c _60056) (@lem4843664 A P u s Q Q' h1)). Qed.
Lemma lem4843723 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term199 A P c _60056 u) = (term200 A P c _60056 u).
Proof. exact (eq_refl (term199 A P c _60056 u)). Qed.
Lemma lem4843724 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term201 A P c _60056 s) = (term201 A P c _60056 s).
Proof. exact (eq_refl (term201 A P c _60056 s)). Qed.
Lemma lem4843725 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term198 A P c _60056 s) = (term199 A P c _60056 u)) = ((term198 A P c _60056 s) = (term200 A P c _60056 u)).
Proof. exact (MK_COMB (@lem4843724 A P c _60056 s) (@lem4843723 A P c _60056 u)). Qed.
Lemma lem4843726 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term198 A P c _60056 s) = (term195 A P c _60056 s).
Proof. exact (eq_refl (term198 A P c _60056 s)). Qed.
Lemma lem4843727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843728 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term201 A P c _60056 s) = (term202 A P c _60056 s).
Proof. exact (MK_COMB (@lem4843727) (@lem4843726 A P c _60056 s)). Qed.
Lemma lem4843729 {A : Type'} (P : type180 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term200 A P c _60056 u) = (term200 A P c _60056 u).
Proof. exact (eq_refl (term200 A P c _60056 u)). Qed.
Lemma lem4843730 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term198 A P c _60056 s) = (term200 A P c _60056 u)) = ((term195 A P c _60056 s) = (term200 A P c _60056 u)).
Proof. exact (MK_COMB (@lem4843728 A P c _60056 s) (@lem4843729 A P c _60056 u)). Qed.
Lemma lem4843731 {A : Type'} (s : A -> Prop) (P : type180 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term198 A P c _60056 s) = (term199 A P c _60056 u)) = ((term195 A P c _60056 s) = (term200 A P c _60056 u)).
Proof. exact (TRANS (@lem4843725 A s P c _60056 u) (@lem4843730 A s P c _60056 u)). Qed.
Lemma lem4843732 {A : Type'} (c : type178 A) (_60056 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term195 A P c _60056 s) = (term200 A P c _60056 u).
Proof. exact (EQ_MP (@lem4843731 A s P c _60056 u) (@lem4843722 A c _60056 P u s Q Q' h1)). Qed.
Lemma lem4843733 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term200 A P c _60056 u.
Proof. exact (EQ_MP (@lem4843732 A c _60056 P u s Q Q' h2) (@lem4843653 A _60056 P Q' c s h1)). Qed.
Lemma lem4843734 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) : (term203 A P Q' c _60056) = (term203 A P Q' c _60056).
Proof. exact (eq_refl (term203 A P Q' c _60056)). Qed.
Lemma lem4843735 {A : Type'} (c : type178 A) (_60056 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term204 A P Q' c _60056 s) = (term205 A P Q' c _60056 u).
Proof. exact (MK_COMB (@lem4843734 A P Q' c _60056) (@lem4843664 A P u s Q Q' h1)). Qed.
Lemma lem4843736 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term205 A P Q' c _60056 u) = (term206 A P Q' c _60056 u).
Proof. exact (eq_refl (term205 A P Q' c _60056 u)). Qed.
Lemma lem4843737 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term207 A P Q' c _60056 s) = (term207 A P Q' c _60056 s).
Proof. exact (eq_refl (term207 A P Q' c _60056 s)). Qed.
Lemma lem4843738 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term204 A P Q' c _60056 s) = (term205 A P Q' c _60056 u)) = ((term204 A P Q' c _60056 s) = (term206 A P Q' c _60056 u)).
Proof. exact (MK_COMB (@lem4843737 A P Q' c _60056 s) (@lem4843736 A P Q' c _60056 u)). Qed.
Lemma lem4843739 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term204 A P Q' c _60056 s) = (term196 A P Q' c _60056 s).
Proof. exact (eq_refl (term204 A P Q' c _60056 s)). Qed.
Lemma lem4843740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843741 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (s : A -> Prop) : (term207 A P Q' c _60056 s) = (term208 A P Q' c _60056 s).
Proof. exact (MK_COMB (@lem4843740) (@lem4843739 A P Q' c _60056 s)). Qed.
Lemma lem4843742 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term206 A P Q' c _60056 u) = (term206 A P Q' c _60056 u).
Proof. exact (eq_refl (term206 A P Q' c _60056 u)). Qed.
Lemma lem4843743 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term204 A P Q' c _60056 s) = (term206 A P Q' c _60056 u)) = ((term196 A P Q' c _60056 s) = (term206 A P Q' c _60056 u)).
Proof. exact (MK_COMB (@lem4843741 A P Q' c _60056 s) (@lem4843742 A P Q' c _60056 u)). Qed.
Lemma lem4843744 {A : Type'} (s : A -> Prop) (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : ((term204 A P Q' c _60056 s) = (term205 A P Q' c _60056 u)) = ((term196 A P Q' c _60056 s) = (term206 A P Q' c _60056 u)).
Proof. exact (TRANS (@lem4843738 A s P Q' c _60056 u) (@lem4843743 A s P Q' c _60056 u)). Qed.
Lemma lem4843745 {A : Type'} (c : type178 A) (_60056 : type686 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : (term196 A P Q' c _60056 s) = (term206 A P Q' c _60056 u).
Proof. exact (EQ_MP (@lem4843744 A s P Q' c _60056 u) (@lem4843735 A c _60056 P u s Q Q' h1)). Qed.
Lemma lem4843746 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term206 A P Q' c _60056 u.
Proof. exact (EQ_MP (@lem4843745 A c _60056 P u s Q Q' h2) (@lem4843663 A _60056 P Q' c s h1)). Qed.
Lemma lem4843823 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (proj1 (@lem4843543 A P u s Q Q' h1)). Qed.
Lemma lem4843824 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term209 A P u.
Proof. exact (fun h0 : term144 A P u => @lem4843823 A P u s Q Q' h1). Qed.
Lemma lem4843826 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4843827 {A : Type'} (P : type180 A) (u : type686 A) : (term209 A P u) = (P u).
Proof. exact (@lem4843826 (P u)). Qed.
Lemma lem4843828 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (EQ_MP (@lem4843827 A P u) (@lem4843824 A P u s Q Q' h1)). Qed.
Lemma lem4843830 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (proj1 (@lem4843543 A P u s Q Q' h1)). Qed.
Lemma lem4843831 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term209 A P u.
Proof. exact (fun h0 : term144 A P u => @lem4843830 A P u s Q Q' h1). Qed.
Lemma lem4843833 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4843834 {A : Type'} (P : type180 A) (u : type686 A) : (term209 A P u) = (P u).
Proof. exact (@lem4843833 (P u)). Qed.
Lemma lem4843835 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : P u.
Proof. exact (EQ_MP (@lem4843834 A P u) (@lem4843831 A P u s Q Q' h1)). Qed.
Lemma lem4843837 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4843838 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4843837 A x). Qed.
Lemma lem4843839 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (@lem4843838 A (@UNIONS A u)). Qed.
Lemma lem4843840 {A : Type'} (u : type686 A) : term211 A u.
Proof. exact (fun h0 : term212 A u => @lem4843839 A u). Qed.
Lemma lem4843842 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4843843 {A : Type'} (u : type686 A) : (term211 A u) = ((@UNIONS A u) = (@UNIONS A u)).
Proof. exact (@lem4843842 ((@UNIONS A u) = (@UNIONS A u))). Qed.
Lemma lem4843844 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4843843 A u) (@lem4843840 A u)). Qed.
Lemma lem4843850 (q : Prop) (p : Prop) (r : Prop) : (term213 p q r) = (term213 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4843851 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term200 A P c _60056 u) = (term214 A c P _60056 u).
Proof. exact (@lem4843850 (term184 A c _60056) (term144 A P _60056) (term215 A _60056 u)). Qed.
Lemma lem4843869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843870 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term216 A P c _60056 u) = (term217 A c P _60056 u).
Proof. exact (MK_COMB (@lem4843869) (@lem4843851 A c P _60056 u)). Qed.
Lemma lem4843888 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term214 A c P _60056 u) = (term214 A c P _60056 u).
Proof. exact (eq_refl (term214 A c P _60056 u)). Qed.
Lemma lem4843889 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : ((term200 A P c _60056 u) = (term214 A c P _60056 u)) = ((term214 A c P _60056 u) = (term214 A c P _60056 u)).
Proof. exact (MK_COMB (@lem4843870 A c P _60056 u) (@lem4843888 A c P _60056 u)). Qed.
Lemma lem4843891 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4843892 (x : Prop) : (x = x) = True.
Proof. exact (@lem4843891 Prop x). Qed.
Lemma lem4843893 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : ((term214 A c P _60056 u) = (term214 A c P _60056 u)) = True.
Proof. exact (@lem4843892 (term214 A c P _60056 u)). Qed.
Lemma lem4843894 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : ((term200 A P c _60056 u) = (term214 A c P _60056 u)) = True.
Proof. exact (TRANS (@lem4843889 A c P _60056 u) (@lem4843893 A c P _60056 u)). Qed.
Lemma lem4843895 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : True = ((term200 A P c _60056 u) = (term214 A c P _60056 u)).
Proof. exact (SYM (@lem4843894 A c P _60056 u)). Qed.
Lemma lem4843896 {A : Type'} (c : type178 A) (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term200 A P c _60056 u) = (term214 A c P _60056 u).
Proof. exact (EQ_MP (@lem4843895 A c P _60056 u) (@lem0)). Qed.
Lemma lem4843897 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term214 A c P _60056 u.
Proof. exact (EQ_MP (@lem4843896 A c P _60056 u) (@lem4843733 A _60056 c P u s Q Q' h1 h2)). Qed.
Lemma lem4843899 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4843900 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60056 : type686 A) : (term214 A c P _60056 u) = (term219 A P u c _60056).
Proof. exact (@lem4843899 (term220 A P _60056 u) (term184 A c _60056)). Qed.
Lemma lem4843902 (a : Prop) (b : Prop) : (term221 a b) = (term222 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4843903 {A : Type'} (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term223 A P _60056 u) = (term224 A P _60056 u).
Proof. exact (@lem4843902 (term144 A P _60056) (term215 A _60056 u)). Qed.
Lemma lem4843905 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4843906 {A : Type'} (P : type180 A) (_60056 : type686 A) : (term225 A P _60056) = (P _60056).
Proof. exact (@lem4843905 (P _60056)). Qed.
Lemma lem4843907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4843908 {A : Type'} (P : type180 A) (_60056 : type686 A) : (term226 A P _60056) = (term50 A P _60056).
Proof. exact (MK_COMB (@lem4843907) (@lem4843906 A P _60056)). Qed.
Lemma lem4843910 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4843911 {A : Type'} (_60056 : type686 A) (u : type686 A) : (term227 A _60056 u) = ((@UNIONS A _60056) = (@UNIONS A u)).
Proof. exact (@lem4843910 ((@UNIONS A _60056) = (@UNIONS A u))). Qed.
Lemma lem4843912 {A : Type'} (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term224 A P _60056 u) = (term228 A P _60056 u).
Proof. exact (MK_COMB (@lem4843908 A P _60056) (@lem4843911 A _60056 u)). Qed.
Lemma lem4843913 {A : Type'} (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term223 A P _60056 u) = (term228 A P _60056 u).
Proof. exact (TRANS (@lem4843903 A P _60056 u) (@lem4843912 A P _60056 u)). Qed.
Lemma lem4843914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4843915 {A : Type'} (P : type180 A) (_60056 : type686 A) (u : type686 A) : (term229 A P _60056 u) = (term230 A P _60056 u).
Proof. exact (MK_COMB (@lem4843914) (@lem4843913 A P _60056 u)). Qed.
Lemma lem4843916 {A : Type'} (c : type178 A) (_60056 : type686 A) : (term184 A c _60056) = (term184 A c _60056).
Proof. exact (eq_refl (term184 A c _60056)). Qed.
Lemma lem4843917 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60056 : type686 A) : (term219 A P u c _60056) = (term231 A P u c _60056).
Proof. exact (MK_COMB (@lem4843915 A P _60056 u) (@lem4843916 A c _60056)). Qed.
Lemma lem4843918 {A : Type'} (P : type180 A) (u : type686 A) (c : type178 A) (_60056 : type686 A) : (term214 A c P _60056 u) = (term231 A P u c _60056).
Proof. exact (TRANS (@lem4843900 A P u c _60056) (@lem4843917 A P u c _60056)). Qed.
Lemma lem4843920 {A : Type'} (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term232 A P u.
Proof. exact (conj (@lem4843835 A P u s Q Q' h1) (@lem4843844 A u)). Qed.
Lemma lem4843922 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term231 A P u c _60056.
Proof. exact (EQ_MP (@lem4843918 A P u c _60056) (@lem4843897 A _60056 c P u s Q Q' h1 h2)). Qed.
Lemma lem4843923 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term231 A P u c _60056.
Proof. exact (@lem4843922 A _60056 c P u s Q Q' h1 h2). Qed.
Lemma lem4843924 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term233 A P c u.
Proof. exact (@lem4843923 A u c P u s Q Q' h1 h2). Qed.
Lemma lem4843927 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term184 A c u.
Proof. exact (@lem4843924 A c P u s Q Q' h1 h2 (@lem4843920 A P u s Q Q' h2)). Qed.
Lemma lem4843928 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term234 A c u.
Proof. exact (fun h0 : term235 A c u => @lem4843927 A c P u s Q Q' h1 h2). Qed.
Lemma lem4843930 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4843931 {A : Type'} (c : type178 A) (u : type686 A) : (term234 A c u) = (term184 A c u).
Proof. exact (@lem4843930 (term184 A c u)). Qed.
Lemma lem4843932 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term184 A c u.
Proof. exact (EQ_MP (@lem4843931 A c u) (@lem4843928 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4843938 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4843939 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : (term57 A u Q _60058) = (term236 A Q _60058 u).
Proof. exact (@lem4843938 (Q _60058) (term237 A _60058 u)). Qed.
Lemma lem4843945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843946 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : (term238 A u Q _60058) = (term239 A Q _60058 u).
Proof. exact (MK_COMB (@lem4843945) (@lem4843939 A Q _60058 u)). Qed.
Lemma lem4843952 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : (term236 A Q _60058 u) = (term236 A Q _60058 u).
Proof. exact (eq_refl (term236 A Q _60058 u)). Qed.
Lemma lem4843953 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : ((term57 A u Q _60058) = (term236 A Q _60058 u)) = ((term236 A Q _60058 u) = (term236 A Q _60058 u)).
Proof. exact (MK_COMB (@lem4843946 A Q _60058 u) (@lem4843952 A Q _60058 u)). Qed.
Lemma lem4843955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4843956 (x : Prop) : (x = x) = True.
Proof. exact (@lem4843955 Prop x). Qed.
Lemma lem4843957 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : ((term236 A Q _60058 u) = (term236 A Q _60058 u)) = True.
Proof. exact (@lem4843956 (term236 A Q _60058 u)). Qed.
Lemma lem4843958 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : ((term57 A u Q _60058) = (term236 A Q _60058 u)) = True.
Proof. exact (TRANS (@lem4843953 A Q _60058 u) (@lem4843957 A Q _60058 u)). Qed.
Lemma lem4843959 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : True = ((term57 A u Q _60058) = (term236 A Q _60058 u)).
Proof. exact (SYM (@lem4843958 A Q _60058 u)). Qed.
Lemma lem4843960 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) (u : type686 A) : (term57 A u Q _60058) = (term236 A Q _60058 u).
Proof. exact (EQ_MP (@lem4843959 A Q _60058 u) (@lem0)). Qed.
Lemma lem4843961 {A : Type'} (_60058 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term236 A Q _60058 u.
Proof. exact (EQ_MP (@lem4843960 A Q _60058 u) (@lem4843720 A _60058 P u s Q Q' h1)). Qed.
Lemma lem4843963 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4843964 {A : Type'} (u : type686 A) (Q : type686 A) (_60058 : A -> Prop) : (term236 A Q _60058 u) = (term240 A u Q _60058).
Proof. exact (@lem4843963 (term237 A _60058 u) (Q _60058)). Qed.
Lemma lem4843966 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4843967 {A : Type'} (_60058 : A -> Prop) (u : type686 A) : (term241 A _60058 u) = (@IN (A -> Prop) _60058 u).
Proof. exact (@lem4843966 (@IN (A -> Prop) _60058 u)). Qed.
Lemma lem4843968 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4843969 {A : Type'} (_60058 : A -> Prop) (u : type686 A) : (term242 A _60058 u) = (term243 A _60058 u).
Proof. exact (MK_COMB (@lem4843968) (@lem4843967 A _60058 u)). Qed.
Lemma lem4843970 {A : Type'} (Q : type686 A) (_60058 : A -> Prop) : (Q _60058) = (Q _60058).
Proof. exact (eq_refl (Q _60058)). Qed.
Lemma lem4843971 {A : Type'} (u : type686 A) (Q : type686 A) (_60058 : A -> Prop) : (term240 A u Q _60058) = (term45 A u Q _60058).
Proof. exact (MK_COMB (@lem4843969 A _60058 u) (@lem4843970 A Q _60058)). Qed.
Lemma lem4843972 {A : Type'} (u : type686 A) (Q : type686 A) (_60058 : A -> Prop) : (term236 A Q _60058 u) = (term45 A u Q _60058).
Proof. exact (TRANS (@lem4843964 A u Q _60058) (@lem4843971 A u Q _60058)). Qed.
Lemma lem4843975 {A : Type'} (_60058 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term45 A u Q _60058.
Proof. exact (EQ_MP (@lem4843972 A u Q _60058) (@lem4843961 A _60058 P u s Q Q' h1)). Qed.
Lemma lem4843976 {A : Type'} (_60058 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term45 A u Q _60058.
Proof. exact (@lem4843975 A _60058 P u s Q Q' h1). Qed.
Lemma lem4843977 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term244 A Q c u.
Proof. exact (@lem4843976 A (c u) P u s Q Q' h1). Qed.
Lemma lem4843980 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q c u.
Proof. exact (@lem4843977 A c P u s Q Q' h2 (@lem4843932 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4843981 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term246 A Q c u.
Proof. exact (fun h0 : term185 A Q c u => @lem4843980 A c P u s Q Q' h1 h2). Qed.
Lemma lem4843983 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4843984 {A : Type'} (Q : type686 A) (c : type178 A) (u : type686 A) : (term246 A Q c u) = (term245 A Q c u).
Proof. exact (@lem4843983 (term245 A Q c u)). Qed.
Lemma lem4843985 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q c u.
Proof. exact (EQ_MP (@lem4843984 A Q c u) (@lem4843981 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4843991 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4843992 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : (term65 A Q Q' _60057) = (term247 A Q' Q _60057).
Proof. exact (@lem4843991 (Q' _60057) (term248 A Q _60057)). Qed.
Lemma lem4843998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4843999 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : (term249 A Q Q' _60057) = (term250 A Q' Q _60057).
Proof. exact (MK_COMB (@lem4843998) (@lem4843992 A Q' Q _60057)). Qed.
Lemma lem4844005 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : (term247 A Q' Q _60057) = (term247 A Q' Q _60057).
Proof. exact (eq_refl (term247 A Q' Q _60057)). Qed.
Lemma lem4844006 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : ((term65 A Q Q' _60057) = (term247 A Q' Q _60057)) = ((term247 A Q' Q _60057) = (term247 A Q' Q _60057)).
Proof. exact (MK_COMB (@lem4843999 A Q' Q _60057) (@lem4844005 A Q' Q _60057)). Qed.
Lemma lem4844008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4844009 (x : Prop) : (x = x) = True.
Proof. exact (@lem4844008 Prop x). Qed.
Lemma lem4844010 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : ((term247 A Q' Q _60057) = (term247 A Q' Q _60057)) = True.
Proof. exact (@lem4844009 (term247 A Q' Q _60057)). Qed.
Lemma lem4844011 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : ((term65 A Q Q' _60057) = (term247 A Q' Q _60057)) = True.
Proof. exact (TRANS (@lem4844006 A Q' Q _60057) (@lem4844010 A Q' Q _60057)). Qed.
Lemma lem4844012 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : True = ((term65 A Q Q' _60057) = (term247 A Q' Q _60057)).
Proof. exact (SYM (@lem4844011 A Q' Q _60057)). Qed.
Lemma lem4844013 {A : Type'} (Q' : type686 A) (Q : type686 A) (_60057 : A -> Prop) : (term65 A Q Q' _60057) = (term247 A Q' Q _60057).
Proof. exact (EQ_MP (@lem4844012 A Q' Q _60057) (@lem0)). Qed.
Lemma lem4844014 {A : Type'} (_60057 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term247 A Q' Q _60057.
Proof. exact (EQ_MP (@lem4844013 A Q' Q _60057) (@lem4843692 A _60057 P u s Q Q' h1)). Qed.
Lemma lem4844016 (b : Prop) (a : Prop) : (a \/ b) = (term218 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4844017 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60057 : A -> Prop) : (term247 A Q' Q _60057) = (term251 A Q Q' _60057).
Proof. exact (@lem4844016 (term248 A Q _60057) (Q' _60057)). Qed.
Lemma lem4844019 (a : Prop) : (term44 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4844020 {A : Type'} (Q : type686 A) (_60057 : A -> Prop) : (term252 A Q _60057) = (Q _60057).
Proof. exact (@lem4844019 (Q _60057)). Qed.
Lemma lem4844021 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4844022 {A : Type'} (Q : type686 A) (_60057 : A -> Prop) : (term253 A Q _60057) = (term254 A Q _60057).
Proof. exact (MK_COMB (@lem4844021) (@lem4844020 A Q _60057)). Qed.
Lemma lem4844023 {A : Type'} (Q' : type686 A) (_60057 : A -> Prop) : (Q' _60057) = (Q' _60057).
Proof. exact (eq_refl (Q' _60057)). Qed.
Lemma lem4844024 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60057 : A -> Prop) : (term251 A Q Q' _60057) = (term53 A Q Q' _60057).
Proof. exact (MK_COMB (@lem4844022 A Q _60057) (@lem4844023 A Q' _60057)). Qed.
Lemma lem4844025 {A : Type'} (Q : type686 A) (Q' : type686 A) (_60057 : A -> Prop) : (term247 A Q' Q _60057) = (term53 A Q Q' _60057).
Proof. exact (TRANS (@lem4844017 A Q Q' _60057) (@lem4844024 A Q Q' _60057)). Qed.
Lemma lem4844028 {A : Type'} (_60057 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term53 A Q Q' _60057.
Proof. exact (EQ_MP (@lem4844025 A Q Q' _60057) (@lem4844014 A _60057 P u s Q Q' h1)). Qed.
Lemma lem4844029 {A : Type'} (_60057 : A -> Prop) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term53 A Q Q' _60057.
Proof. exact (@lem4844028 A _60057 P u s Q Q' h1). Qed.
Lemma lem4844030 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term85 A P u s Q Q') : term255 A Q Q' c u.
Proof. exact (@lem4844029 A (c u) P u s Q Q' h1). Qed.
Lemma lem4844033 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q' c u.
Proof. exact (@lem4844030 A c P u s Q Q' h2 (@lem4843985 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4844034 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term246 A Q' c u.
Proof. exact (fun h0 : term185 A Q' c u => @lem4844033 A c P u s Q Q' h1 h2). Qed.
Lemma lem4844036 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4844037 {A : Type'} (Q' : type686 A) (c : type178 A) (u : type686 A) : (term246 A Q' c u) = (term245 A Q' c u).
Proof. exact (@lem4844036 (term245 A Q' c u)). Qed.
Lemma lem4844038 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term245 A Q' c u.
Proof. exact (EQ_MP (@lem4844037 A Q' c u) (@lem4844034 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4844040 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem4844041 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem4844040 A x). Qed.
Lemma lem4844042 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (@lem4844041 A (@UNIONS A u)). Qed.
Lemma lem4844043 {A : Type'} (u : type686 A) : term211 A u.
Proof. exact (fun h0 : term212 A u => @lem4844042 A u). Qed.
Lemma lem4844045 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4844046 {A : Type'} (u : type686 A) : (term211 A u) = ((@UNIONS A u) = (@UNIONS A u)).
Proof. exact (@lem4844045 ((@UNIONS A u) = (@UNIONS A u))). Qed.
Lemma lem4844047 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (EQ_MP (@lem4844046 A u) (@lem4844043 A u)). Qed.
Lemma lem4844049 (a : Prop) (b : Prop) : (term256 a b) = (term257 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4844050 {A : Type'} (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term258 A Q' c _60056 u) = (term259 A Q' c _60056 u).
Proof. exact (@lem4844049 (term245 A Q' c _60056) ((@UNIONS A _60056) = (@UNIONS A u))). Qed.
Lemma lem4844051 {A : Type'} (P : type180 A) (_60056 : type686 A) : (term106 A P _60056) = (term106 A P _60056).
Proof. exact (eq_refl (term106 A P _60056)). Qed.
Lemma lem4844052 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term206 A P Q' c _60056 u) = (term260 A P Q' c _60056 u).
Proof. exact (MK_COMB (@lem4844051 A P _60056) (@lem4844050 A Q' c _60056 u)). Qed.
Lemma lem4844054 (a : Prop) (b : Prop) : (term256 a b) = (term257 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4844055 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term260 A P Q' c _60056 u) = (term261 A P Q' c _60056 u).
Proof. exact (@lem4844054 (P _60056) (term262 A Q' c _60056 u)). Qed.
Lemma lem4844056 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term206 A P Q' c _60056 u) = (term261 A P Q' c _60056 u).
Proof. exact (TRANS (@lem4844052 A P Q' c _60056 u) (@lem4844055 A P Q' c _60056 u)). Qed.
Lemma lem4844058 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4844059 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term261 A P Q' c _60056 u) = (term263 A P Q' c _60056 u).
Proof. exact (@lem4844058 (term264 A P Q' c _60056 u)). Qed.
Lemma lem4844060 {A : Type'} (P : type180 A) (Q' : type686 A) (c : type178 A) (_60056 : type686 A) (u : type686 A) : (term206 A P Q' c _60056 u) = (term263 A P Q' c _60056 u).
Proof. exact (TRANS (@lem4844056 A P Q' c _60056 u) (@lem4844059 A P Q' c _60056 u)). Qed.
Lemma lem4844062 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term265 A Q' c u.
Proof. exact (conj (@lem4844038 A c P u s Q Q' h1 h2) (@lem4844047 A u)). Qed.
Lemma lem4844063 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term266 A P Q' c u.
Proof. exact (conj (@lem4843828 A P u s Q Q' h2) (@lem4844062 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4844065 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term263 A P Q' c _60056 u.
Proof. exact (EQ_MP (@lem4844060 A P Q' c _60056 u) (@lem4843746 A _60056 c P u s Q Q' h1 h2)). Qed.
Lemma lem4844066 {A : Type'} (_60056 : type686 A) (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term263 A P Q' c _60056 u.
Proof. exact (@lem4844065 A _60056 c P u s Q Q' h1 h2). Qed.
Lemma lem4844067 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term267 A P Q' c u.
Proof. exact (@lem4844066 A u c P u s Q Q' h1 h2). Qed.
Lemma lem4844070 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (@lem4844067 A c P u s Q Q' h1 h2 (@lem4844063 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4844071 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : term268.
Proof. exact (fun h0 : ~ False => @lem4844070 A c P u s Q Q' h1 h2). Qed.
Lemma lem4844073 (p : Prop) : (term210 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4844074 : term268 = False.
Proof. exact (@lem4844073 False). Qed.
Lemma lem4844076 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4844074) (@lem4844071 A c P u s Q Q' h1 h2)). Qed.
Lemma lem4844077 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : (term85 A P u s Q Q') = False.
Proof. exact (prop_ext (fun h3 : term85 A P u s Q Q' => @lem4844076 A c P u s Q Q' h1 h2) (fun h3 : False => @lem4843541 A P u s Q Q' h2)). Qed.
Lemma lem4844078 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4844077 A c P u s Q Q' h1 h2) (@lem4843541 A P u s Q Q' h2)). Qed.
Lemma lem4844079 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : (term178 A P Q' c s) = False.
Proof. exact (prop_ext (fun h3 : term178 A P Q' c s => @lem4844078 A c P u s Q Q' h1 h2) (fun h3 : False => @lem4843491 A P Q' c s h1)). Qed.
Lemma lem4844080 {A : Type'} (c : type178 A) (P : type180 A) (u : type686 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term85 A P u s Q Q') : False.
Proof. exact (EQ_MP (@lem4844079 A c P u s Q Q' h1 h2) (@lem4843491 A P Q' c s h1)). Qed.
Lemma lem4844081 {A : Type'} (c : type178 A) (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term178 A P Q' c s) (h2 : term16 A P s Q Q') : False.
Proof. exact (ex_elim (@lem4843228 A P s Q Q' h2) (fun u : type686 A => fun h0 : term87 A P s Q Q' u => @lem4844080 A c P u s Q Q' h1 h0)). Qed.
Lemma lem4844082 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : False.
Proof. exact (ex_elim (@lem4843448 A P Q' s h1) (fun c : type178 A => fun h0 : term180 A P Q' s c => @lem4844081 A c P s Q Q' h0 h2)). Qed.
Lemma lem4844083 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : (term56 A P Q' s) = False.
Proof. exact (prop_ext (fun h3 : term56 A P Q' s => @lem4844082 A P s Q Q' h1 h2) (fun h3 : False => @lem4843074 A P Q' s h1)). Qed.
Lemma lem4844084 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term56 A P Q' s) (h2 : term16 A P s Q Q') : False.
Proof. exact (EQ_MP (@lem4844083 A P s Q Q' h1 h2) (@lem4843074 A P Q' s h1)). Qed.
Lemma lem4844085 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term55 A P Q' s.
Proof. exact (fun h0 : term56 A P Q' s => @lem4844084 A P s Q Q' h0 h1). Qed.
Lemma lem4844086 {A : Type'} (P : type180 A) (s : A -> Prop) (Q : type686 A) (Q' : type686 A) (h1 : term16 A P s Q Q') : term8 A P Q' s.
Proof. exact (EQ_MP (@lem4843073 A P Q' s) (@lem4844085 A P s Q Q' h1)). Qed.
Lemma lem4844087 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) (s : A -> Prop) : term20 A Q P Q' s.
Proof. exact (fun h0 : term16 A P s Q Q' => @lem4844086 A P s Q Q' h0). Qed.
Lemma lem4844092 {A : Type'} (Q : type686 A) (P : type180 A) (Q' : type686 A) : term24 A Q P Q'.
Proof. exact (fun s : A -> Prop => @lem4844087 A Q P Q' s). Qed.
Lemma lem4844097 {A : Type'} (Q : type686 A) (P : type180 A) : term28 A Q P.
Proof. exact (fun Q' : type686 A => @lem4844092 A Q P Q'). Qed.
Lemma lem4844102 {A : Type'} (P : type180 A) : term32 A P.
Proof. exact (fun Q : type686 A => @lem4844097 A Q P). Qed.
Lemma lem4844107 {A : Type'} : term36 A.
Proof. exact (fun P : type180 A => @lem4844102 A P). Qed.
Lemma lem4844108 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem4843068 A) (@lem4844107 A)). Qed.
Lemma lem4844110 {A : Type'} : term38 A.
Proof. exact (@lem4842815 A (@lem4844108 A)). Qed.
Lemma lem4844111 {A : Type'} (h1 : term39 A) : False.
Proof. exact (@lem4844110 A (@lem4842799 A h1)). Qed.
Lemma lem4844112 {A : Type'} (h1 : term39 A) : (term39 A) = False.
Proof. exact (prop_ext (fun h2 : term39 A => @lem4844111 A h1) (fun h2 : False => @lem4842799 A h1)). Qed.
Lemma lem4844113 {A : Type'} (h1 : term39 A) : False.
Proof. exact (EQ_MP (@lem4844112 A h1) (@lem4842799 A h1)). Qed.
Lemma lem4844114 {A : Type'} : term38 A.
Proof. exact (fun h0 : term39 A => @lem4844113 A h0). Qed.
Lemma lem4844115 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem4842798 A) (@lem4844114 A)). Qed.
Lemma lem4844116 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4842794 A) (@lem4844115 A)). Qed.
