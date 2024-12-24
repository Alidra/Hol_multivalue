Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA6_term_abbrevs.
Require Import LE_ADD_spec.
Require Import LE_ADDR_spec.
Require Import LE_MULT2_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_MULT_RCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_AC_spec.
Require Import MULT_ASSOC_spec.
Require Import NADD_LBOUND_spec.
Require Import NADD_MUL_LINV_LEMMA5_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1303797 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303798 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1303797 h1 m). Qed.
Lemma lem1303799 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1303800 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1303799 m) (@lem1303798 m h1)). Qed.
Lemma lem1303801 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1303800 m h1 n). Qed.
Lemma lem1303802 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1303803 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1303802 n m) (@lem1303801 m n h1)). Qed.
Lemma lem1303804 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1303803 n m h1 p). Qed.
Lemma lem1303805 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1303806 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1303805 n m p) (@lem1303804 n m p h1)). Qed.
Lemma lem1303807 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1303808 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1303806 n m p h1 (@lem1303807 m n p h2)). Qed.
Lemma lem1303809 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1303808 m n p h0 h1). Qed.
Lemma lem1303810 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1303811 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1303810 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1303809 m n p h0)). Qed.
Lemma lem1303812 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1303813 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1303811 m p h2 (@lem1303812 h1)). Qed.
Lemma lem1303814 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1303813 m p h1 h0). Qed.
Lemma lem1303815 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1303814 m p h1). Qed.
Lemma lem1303816 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1303815 m h1). Qed.
Lemma lem1303817 : term14.
Proof. exact (fun h0 : term0 => @lem1303816 h0). Qed.
Lemma lem1303818 : term13.
Proof. exact (@lem1303817 (@lem93743)). Qed.
Lemma lem1303819 (m : nat) : term15 m.
Proof. exact (@lem1303818 m). Qed.
Lemma lem1303820 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1303821 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1303820 m) (@lem1303819 m)). Qed.
Lemma lem1303822 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1303821 m p). Qed.
Lemma lem1303823 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1303825 (m : nat) : term17 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1303826 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem1303827 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem1303826 m) (@lem1303825 m)). Qed.
Lemma lem1303828 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1303827 m n). Qed.
Lemma lem1303829 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1303830 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem1303829 m n) (@lem1303828 m n)). Qed.
Lemma lem1303831 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem1303830 m n p). Qed.
Lemma lem1303832 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 n m p) = (term23 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem1303834 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1303835 {A : Type'} (x : A) : (term24 A x) = ((x = x) = True).
Proof. exact (eq_refl (term24 A x)). Qed.
Lemma lem1303837 (n : nat) (m : nat) (p : nat) : term25 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1303844 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1303837 n m p)). Qed.
Lemma lem1303845 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term28 a b c d e f) = (term29 a b c d e f).
Proof. exact (@lem1303844 a (Nat.mul b c) (term26 d e f)). Qed.
Lemma lem1303853 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1303837 n m p)). Qed.
Lemma lem1303854 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term30 b c d e f) = (term31 b c d e f).
Proof. exact (@lem1303853 b c (term26 d e f)). Qed.
Lemma lem1303868 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1303837 n m p)). Qed.
Lemma lem1303869 (d : nat) (e : nat) (f : nat) : (term26 d e f) = (term27 d e f).
Proof. exact (@lem1303868 d e f). Qed.
Lemma lem1303879 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem1303880 (c : nat) (d : nat) (e : nat) (f : nat) : (term32 c d e f) = (term33 c d e f).
Proof. exact (MK_COMB (@lem1303879 c) (@lem1303869 d e f)). Qed.
Lemma lem1303887 (b : nat) : (Nat.mul b) = (Nat.mul b).
Proof. exact (eq_refl (Nat.mul b)). Qed.
Lemma lem1303888 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term31 b c d e f) = (term34 b c d e f).
Proof. exact (MK_COMB (@lem1303887 b) (@lem1303880 c d e f)). Qed.
Lemma lem1303895 (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term30 b c d e f) = (term34 b c d e f).
Proof. exact (TRANS (@lem1303854 b c d e f) (@lem1303888 b c d e f)). Qed.
Lemma lem1303896 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem1303897 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term29 a b c d e f) = (term35 a b c d e f).
Proof. exact (MK_COMB (@lem1303896 a) (@lem1303895 b c d e f)). Qed.
Lemma lem1303904 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term28 a b c d e f) = (term35 a b c d e f).
Proof. exact (TRANS (@lem1303845 a b c d e f) (@lem1303897 a b c d e f)). Qed.
Lemma lem1303905 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1303906 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term36 a b c d e f) = (term37 a b c d e f).
Proof. exact (MK_COMB (@lem1303905) (@lem1303904 a b c d e f)). Qed.
Lemma lem1303908 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1303837 n m p)). Qed.
Lemma lem1303909 (b : nat) (c : nat) (a : nat) (d : nat) (e : nat) (f : nat) : (term38 b c a d e f) = (term39 b c a d e f).
Proof. exact (@lem1303908 b c (term32 a d e f)). Qed.
Lemma lem1303917 (n : nat) (m : nat) (p : nat) : (term27 m n p) = (term27 n m p).
Proof. exact (proj2 (@lem1303837 n m p)). Qed.
Lemma lem1303918 (a : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term31 c a d e f) = (term31 a c d e f).
Proof. exact (@lem1303917 a c (term26 d e f)). Qed.
Lemma lem1303932 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1303837 n m p)). Qed.
Lemma lem1303933 (d : nat) (e : nat) (f : nat) : (term26 d e f) = (term27 d e f).
Proof. exact (@lem1303932 d e f). Qed.
Lemma lem1303943 (c : nat) : (Nat.mul c) = (Nat.mul c).
Proof. exact (eq_refl (Nat.mul c)). Qed.
Lemma lem1303944 (c : nat) (d : nat) (e : nat) (f : nat) : (term32 c d e f) = (term33 c d e f).
Proof. exact (MK_COMB (@lem1303943 c) (@lem1303933 d e f)). Qed.
Lemma lem1303951 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem1303952 (a : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term31 a c d e f) = (term34 a c d e f).
Proof. exact (MK_COMB (@lem1303951 a) (@lem1303944 c d e f)). Qed.
Lemma lem1303959 (a : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term31 c a d e f) = (term34 a c d e f).
Proof. exact (TRANS (@lem1303918 a c d e f) (@lem1303952 a c d e f)). Qed.
Lemma lem1303960 (b : nat) : (Nat.mul b) = (Nat.mul b).
Proof. exact (eq_refl (Nat.mul b)). Qed.
Lemma lem1303961 (b : nat) (a : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term39 b c a d e f) = (term35 b a c d e f).
Proof. exact (MK_COMB (@lem1303960 b) (@lem1303959 a c d e f)). Qed.
Lemma lem1303963 (n : nat) (m : nat) (p : nat) : (term27 m n p) = (term27 n m p).
Proof. exact (proj2 (@lem1303837 n m p)). Qed.
Lemma lem1303964 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term35 b a c d e f) = (term35 a b c d e f).
Proof. exact (@lem1303963 a b (term33 c d e f)). Qed.
Lemma lem1303992 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term39 b c a d e f) = (term35 a b c d e f).
Proof. exact (TRANS (@lem1303961 b a c d e f) (@lem1303964 a b c d e f)). Qed.
Lemma lem1303993 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : (term38 b c a d e f) = (term35 a b c d e f).
Proof. exact (TRANS (@lem1303909 b c a d e f) (@lem1303992 a b c d e f)). Qed.
Lemma lem1303994 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : ((term28 a b c d e f) = (term38 b c a d e f)) = ((term35 a b c d e f) = (term35 a b c d e f)).
Proof. exact (MK_COMB (@lem1303906 a b c d e f) (@lem1303993 a b c d e f)). Qed.
Lemma lem1303996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1303835 A x) (@lem1303834 A x)). Qed.
Lemma lem1303997 (x : nat) : (x = x) = True.
Proof. exact (@lem1303996 nat x). Qed.
Lemma lem1303998 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) (f : nat) : ((term35 a b c d e f) = (term35 a b c d e f)) = True.
Proof. exact (@lem1303997 (term35 a b c d e f)). Qed.
Lemma lem1303999 (b : nat) (c : nat) (a : nat) (d : nat) (e : nat) (f : nat) : ((term28 a b c d e f) = (term38 b c a d e f)) = True.
Proof. exact (TRANS (@lem1303994 a b c d e f) (@lem1303998 a b c d e f)). Qed.
Lemma lem1304000 (b : nat) (c : nat) (a : nat) (d : nat) (e : nat) (f : nat) : True = ((term28 a b c d e f) = (term38 b c a d e f)).
Proof. exact (SYM (@lem1303999 b c a d e f)). Qed.
Lemma lem1304002 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1304003 (m : nat) (h1 : term40) : term41 m.
Proof. exact (@lem1304002 h1 m). Qed.
Lemma lem1304004 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem1304005 (m : nat) (h1 : term40) : term42 m.
Proof. exact (EQ_MP (@lem1304004 m) (@lem1304003 m h1)). Qed.
Lemma lem1304006 (m : nat) (n : nat) (h1 : term40) : term43 m n.
Proof. exact (@lem1304005 m h1 n). Qed.
Lemma lem1304007 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem1304008 (m : nat) (n : nat) (h1 : term40) : term44 m n.
Proof. exact (EQ_MP (@lem1304007 m n) (@lem1304006 m n h1)). Qed.
Lemma lem1304009 (m : nat) (n : nat) (p : nat) (h1 : term40) : term45 m n p.
Proof. exact (@lem1304008 m n h1 p). Qed.
Lemma lem1304010 (m : nat) (p : nat) (n : nat) : (term45 m n p) = (term46 m p n).
Proof. exact (eq_refl (term45 m n p)). Qed.
Lemma lem1304011 (m : nat) (p : nat) (n : nat) (h1 : term40) : term46 m p n.
Proof. exact (EQ_MP (@lem1304010 m p n) (@lem1304009 m n p h1)). Qed.
Lemma lem1304012 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term40) : term47 m p n q.
Proof. exact (@lem1304011 m p n h1 q). Qed.
Lemma lem1304013 (m : nat) (p : nat) (n : nat) (q : nat) : (term47 m p n q) = (term48 m p n q).
Proof. exact (eq_refl (term47 m p n q)). Qed.
Lemma lem1304014 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term40) : term48 m p n q.
Proof. exact (EQ_MP (@lem1304013 m p n q) (@lem1304012 m p n q h1)). Qed.
Lemma lem1304015 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term49 m n p q) : term49 m n p q.
Proof. exact (h1). Qed.
Lemma lem1304016 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term40) (h2 : term49 m n p q) : term50 m p n q.
Proof. exact (@lem1304014 m p n q h1 (@lem1304015 m n p q h2)). Qed.
Lemma lem1304017 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term49 m n p q) : term51 m p n q.
Proof. exact (fun h0 : term40 => @lem1304016 m n p q h0 h1). Qed.
Lemma lem1304018 (h1 : term40) : term40.
Proof. exact (h1). Qed.
Lemma lem1304019 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term40) (h2 : term49 m n p q) : term50 m p n q.
Proof. exact (@lem1304017 m n p q h2 (@lem1304018 h1)). Qed.
Lemma lem1304020 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term40) : term48 m p n q.
Proof. exact (fun h0 : term49 m n p q => @lem1304019 m n p q h1 h0). Qed.
Lemma lem1304021 (m : nat) (p : nat) (n : nat) (h1 : term40) : term46 m p n.
Proof. exact (fun q : nat => @lem1304020 m p n q h1). Qed.
Lemma lem1304022 (m : nat) (p : nat) (h1 : term40) : term52 m p.
Proof. exact (fun n : nat => @lem1304021 m p n h1). Qed.
Lemma lem1304023 (m : nat) (h1 : term40) : term53 m.
Proof. exact (fun p : nat => @lem1304022 m p h1). Qed.
Lemma lem1304024 (h1 : term40) : term54.
Proof. exact (fun m : nat => @lem1304023 m h1). Qed.
Lemma lem1304025 : term55.
Proof. exact (fun h0 : term40 => @lem1304024 h0). Qed.
Lemma lem1304026 : term54.
Proof. exact (@lem1304025 (@lem102387)). Qed.
Lemma lem1304027 (m : nat) : term56 m.
Proof. exact (@lem1304026 m). Qed.
Lemma lem1304028 (m : nat) : (term56 m) = (term53 m).
Proof. exact (eq_refl (term56 m)). Qed.
Lemma lem1304029 (m : nat) : term53 m.
Proof. exact (EQ_MP (@lem1304028 m) (@lem1304027 m)). Qed.
Lemma lem1304030 (m : nat) (p : nat) : term57 m p.
Proof. exact (@lem1304029 m p). Qed.
Lemma lem1304031 (m : nat) (p : nat) : (term57 m p) = (term52 m p).
Proof. exact (eq_refl (term57 m p)). Qed.
Lemma lem1304032 (m : nat) (p : nat) : term52 m p.
Proof. exact (EQ_MP (@lem1304031 m p) (@lem1304030 m p)). Qed.
Lemma lem1304033 (m : nat) (p : nat) (n : nat) : term58 m p n.
Proof. exact (@lem1304032 m p n). Qed.
Lemma lem1304034 (m : nat) (p : nat) (n : nat) : (term58 m p n) = (term46 m p n).
Proof. exact (eq_refl (term58 m p n)). Qed.
Lemma lem1304035 (m : nat) (p : nat) (n : nat) : term46 m p n.
Proof. exact (EQ_MP (@lem1304034 m p n) (@lem1304033 m p n)). Qed.
Lemma lem1304036 (m : nat) (p : nat) (n : nat) (q : nat) : term47 m p n q.
Proof. exact (@lem1304035 m p n q). Qed.
Lemma lem1304037 (m : nat) (p : nat) (n : nat) (q : nat) : (term47 m p n q) = (term48 m p n q).
Proof. exact (eq_refl (term47 m p n q)). Qed.
Lemma lem1304039 {A : Type'} (x : A) : term24 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1304040 {A : Type'} (x : A) : (term24 A x) = ((x = x) = True).
Proof. exact (eq_refl (term24 A x)). Qed.
Lemma lem1304042 (n : nat) (m : nat) (p : nat) : term25 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem1304049 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1304042 n m p)). Qed.
Lemma lem1304050 (a : nat) (b : nat) (c : nat) (d : nat) : (term59 a b c d) = (term60 a b c d).
Proof. exact (@lem1304049 (Nat.mul a b) c d). Qed.
Lemma lem1304052 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1304042 n m p)). Qed.
Lemma lem1304053 (a : nat) (b : nat) (c : nat) (d : nat) : (term60 a b c d) = (term33 a b c d).
Proof. exact (@lem1304052 a b (Nat.mul c d)). Qed.
Lemma lem1304060 (a : nat) (b : nat) (c : nat) (d : nat) : (term59 a b c d) = (term33 a b c d).
Proof. exact (TRANS (@lem1304050 a b c d) (@lem1304053 a b c d)). Qed.
Lemma lem1304070 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1304071 (a : nat) (b : nat) (c : nat) (d : nat) : (term61 a b c d) = (term62 a b c d).
Proof. exact (MK_COMB (@lem1304070) (@lem1304060 a b c d)). Qed.
Lemma lem1304073 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (proj1 (@lem1304042 n m p)). Qed.
Lemma lem1304074 (a : nat) (c : nat) (b : nat) (d : nat) : (term60 a c b d) = (term33 a c b d).
Proof. exact (@lem1304073 a c (Nat.mul b d)). Qed.
Lemma lem1304082 (n : nat) (m : nat) (p : nat) : (term27 m n p) = (term27 n m p).
Proof. exact (proj2 (@lem1304042 n m p)). Qed.
Lemma lem1304083 (b : nat) (c : nat) (d : nat) : (term27 c b d) = (term27 b c d).
Proof. exact (@lem1304082 b c d). Qed.
Lemma lem1304093 (a : nat) : (Nat.mul a) = (Nat.mul a).
Proof. exact (eq_refl (Nat.mul a)). Qed.
Lemma lem1304094 (a : nat) (b : nat) (c : nat) (d : nat) : (term33 a c b d) = (term33 a b c d).
Proof. exact (MK_COMB (@lem1304093 a) (@lem1304083 b c d)). Qed.
Lemma lem1304101 (a : nat) (b : nat) (c : nat) (d : nat) : (term60 a c b d) = (term33 a b c d).
Proof. exact (TRANS (@lem1304074 a c b d) (@lem1304094 a b c d)). Qed.
Lemma lem1304102 (a : nat) (b : nat) (c : nat) (d : nat) : ((term59 a b c d) = (term60 a c b d)) = ((term33 a b c d) = (term33 a b c d)).
Proof. exact (MK_COMB (@lem1304071 a b c d) (@lem1304101 a b c d)). Qed.
Lemma lem1304104 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1304040 A x) (@lem1304039 A x)). Qed.
Lemma lem1304105 (x : nat) : (x = x) = True.
Proof. exact (@lem1304104 nat x). Qed.
Lemma lem1304106 (a : nat) (b : nat) (c : nat) (d : nat) : ((term33 a b c d) = (term33 a b c d)) = True.
Proof. exact (@lem1304105 (term33 a b c d)). Qed.
Lemma lem1304107 (a : nat) (c : nat) (b : nat) (d : nat) : ((term59 a b c d) = (term60 a c b d)) = True.
Proof. exact (TRANS (@lem1304102 a b c d) (@lem1304106 a b c d)). Qed.
Lemma lem1304108 (a : nat) (c : nat) (b : nat) (d : nat) : True = ((term59 a b c d) = (term60 a c b d)).
Proof. exact (SYM (@lem1304107 a c b d)). Qed.
Lemma lem1304110 (m : nat) : term63 m.
Proof. exact (@lem104289 m). Qed.
Lemma lem1304111 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1304112 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1304111 m) (@lem1304110 m)). Qed.
Lemma lem1304113 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1304112 m n). Qed.
Lemma lem1304114 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1304115 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1304114 m n) (@lem1304113 m n)). Qed.
Lemma lem1304116 (m : nat) (n : nat) (p : nat) : term67 m n p.
Proof. exact (@lem1304115 m n p). Qed.
Lemma lem1304117 (m : nat) (n : nat) (p : nat) : (term67 m n p) = ((term68 m n p) = (term69 m n p)).
Proof. exact (eq_refl (term67 m n p)). Qed.
Lemma lem1304119 (m : nat) : term70 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem1304120 (m : nat) : (term70 m) = (term71 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem1304121 (m : nat) : term71 m.
Proof. exact (EQ_MP (@lem1304120 m) (@lem1304119 m)). Qed.
Lemma lem1304122 (m : nat) (n : nat) : term72 m n.
Proof. exact (@lem1304121 m n). Qed.
Lemma lem1304123 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (eq_refl (term72 m n)). Qed.
Lemma lem1304124 (m : nat) (n : nat) : term73 m n.
Proof. exact (EQ_MP (@lem1304123 m n) (@lem1304122 m n)). Qed.
Lemma lem1304125 (m : nat) (n : nat) (p : nat) : term74 m n p.
Proof. exact (@lem1304124 m n p). Qed.
Lemma lem1304126 (m : nat) (n : nat) (p : nat) : (term74 m n p) = ((term27 m n p) = (term26 m n p)).
Proof. exact (eq_refl (term74 m n p)). Qed.
Lemma lem1304128 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1304129 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem1304128 h1 m). Qed.
Lemma lem1304130 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1304131 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem1304130 m) (@lem1304129 m h1)). Qed.
Lemma lem1304132 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem1304131 m h1 n). Qed.
Lemma lem1304133 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1304134 (n : nat) (m : nat) (h1 : term0) : term4 n m.
Proof. exact (EQ_MP (@lem1304133 n m) (@lem1304132 m n h1)). Qed.
Lemma lem1304135 (n : nat) (m : nat) (p : nat) (h1 : term0) : term5 n m p.
Proof. exact (@lem1304134 n m h1 p). Qed.
Lemma lem1304136 (n : nat) (m : nat) (p : nat) : (term5 n m p) = (term6 n m p).
Proof. exact (eq_refl (term5 n m p)). Qed.
Lemma lem1304137 (n : nat) (m : nat) (p : nat) (h1 : term0) : term6 n m p.
Proof. exact (EQ_MP (@lem1304136 n m p) (@lem1304135 n m p h1)). Qed.
Lemma lem1304138 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term7 m n p.
Proof. exact (h1). Qed.
Lemma lem1304139 (m : nat) (n : nat) (p : nat) (h1 : term0) (h2 : term7 m n p) : Peano.le m p.
Proof. exact (@lem1304137 n m p h1 (@lem1304138 m n p h2)). Qed.
Lemma lem1304140 (m : nat) (n : nat) (p : nat) (h1 : term7 m n p) : term8 m p.
Proof. exact (fun h0 : term0 => @lem1304139 m n p h0 h1). Qed.
Lemma lem1304141 (m : nat) (p : nat) (h1 : term9 m p) : term9 m p.
Proof. exact (h1). Qed.
Lemma lem1304142 (m : nat) (p : nat) (h1 : term9 m p) : term8 m p.
Proof. exact (ex_elim (@lem1304141 m p h1) (fun n : nat => fun h0 : term10 m p n => @lem1304140 m n p h0)). Qed.
Lemma lem1304143 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1304144 (m : nat) (p : nat) (h1 : term0) (h2 : term9 m p) : Peano.le m p.
Proof. exact (@lem1304142 m p h2 (@lem1304143 h1)). Qed.
Lemma lem1304145 (m : nat) (p : nat) (h1 : term0) : term11 m p.
Proof. exact (fun h0 : term9 m p => @lem1304144 m p h1 h0). Qed.
Lemma lem1304146 (m : nat) (h1 : term0) : term12 m.
Proof. exact (fun p : nat => @lem1304145 m p h1). Qed.
Lemma lem1304147 (h1 : term0) : term13.
Proof. exact (fun m : nat => @lem1304146 m h1). Qed.
Lemma lem1304148 : term14.
Proof. exact (fun h0 : term0 => @lem1304147 h0). Qed.
Lemma lem1304149 : term13.
Proof. exact (@lem1304148 (@lem93743)). Qed.
Lemma lem1304150 (m : nat) : term15 m.
Proof. exact (@lem1304149 m). Qed.
Lemma lem1304151 (m : nat) : (term15 m) = (term12 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1304152 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1304151 m) (@lem1304150 m)). Qed.
Lemma lem1304153 (m : nat) (p : nat) : term16 m p.
Proof. exact (@lem1304152 m p). Qed.
Lemma lem1304154 (m : nat) (p : nat) : (term16 m p) = (term11 m p).
Proof. exact (eq_refl (term16 m p)). Qed.
Lemma lem1304156 (x : nadd) : term75 x.
Proof. exact (@lem1300501 x). Qed.
Lemma lem1304157 (x : nadd) : (term75 x) = (term76 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1304159 (x : nadd) : term77 x.
Proof. exact (@lem1303796 x). Qed.
Lemma lem1304160 (x : nadd) : (term77 x) = (term78 x).
Proof. exact (eq_refl (term77 x)). Qed.
Lemma lem1304162 (x : nadd) (h1 : term79 x) : term79 x.
Proof. exact (h1). Qed.
Lemma lem1304164 (x : nadd) : term78 x.
Proof. exact (EQ_MP (@lem1304160 x) (@lem1304159 x)). Qed.
Lemma lem1304165 (x : nadd) (h1 : term79 x) : term80 x.
Proof. exact (@lem1304164 x (@lem1304162 x h1)). Qed.
Lemma lem1304166 (x : nadd) (h1 : term80 x) : term80 x.
Proof. exact (h1). Qed.
Lemma lem1304167 (x : nadd) (B1 : nat) (h1 : term81 x B1) : term81 x B1.
Proof. exact (h1). Qed.
Lemma lem1304168 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term82 N1 x B1.
Proof. exact (h1). Qed.
Lemma lem1304172 (x : nadd) : term76 x.
Proof. exact (EQ_MP (@lem1304157 x) (@lem1304156 x)). Qed.
Lemma lem1304173 (x : nadd) (h1 : term79 x) : term83 x.
Proof. exact (@lem1304172 x (@lem1304162 x h1)). Qed.
Lemma lem1304174 (x : nadd) (h1 : term83 x) : term83 x.
Proof. exact (h1). Qed.
Lemma lem1304175 (B2 : nat) (x : nadd) (h1 : term84 B2 x) : term84 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304176 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304177 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term86 m N1 N2 n) : term86 m N1 N2 n.
Proof. exact (h1). Qed.
Lemma lem1304178 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : term87 N1 N2 n.
Proof. exact (h1). Qed.
Lemma lem1304179 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : term87 N1 N2 m.
Proof. exact (h1). Qed.
Lemma lem1304181 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1304154 m p) (@lem1304153 m p)). Qed.
Lemma lem1304182 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : term88 x B1 B2 m n.
Proof. exact (@lem1304181 (term89 n x m) (term90 B1 B2 m n)). Qed.
Lemma lem1304186 (m : nat) (n : nat) (p : nat) : (term27 m n p) = (term26 m n p).
Proof. exact (EQ_MP (@lem1304126 m n p) (@lem1304125 m n p)). Qed.
Lemma lem1304187 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term91 B2 n x m) = (term92 B2 n x m).
Proof. exact (@lem1304186 (Nat.mul B2 B2) (term93 m x n) (term94 n x m)). Qed.
Lemma lem1304189 (m : nat) (n : nat) (p : nat) : (term27 m n p) = (term26 m n p).
Proof. exact (EQ_MP (@lem1304126 m n p) (@lem1304125 m n p)). Qed.
Lemma lem1304190 (B2 : nat) (m : nat) (x : nadd) (n : nat) : (term95 B2 m x n) = (term96 B2 m x n).
Proof. exact (@lem1304189 (Nat.mul B2 B2) (dest_nadd x m) (dest_nadd x n)). Qed.
Lemma lem1304191 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1304192 (B2 : nat) (m : nat) (x : nadd) (n : nat) : (term97 B2 m x n) = (term98 B2 m x n).
Proof. exact (MK_COMB (@lem1304191) (@lem1304190 B2 m x n)). Qed.
Lemma lem1304193 (n : nat) (x : nadd) (m : nat) : (term94 n x m) = (term94 n x m).
Proof. exact (eq_refl (term94 n x m)). Qed.
Lemma lem1304194 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term92 B2 n x m) = (term99 B2 n x m).
Proof. exact (MK_COMB (@lem1304192 B2 m x n) (@lem1304193 n x m)). Qed.
Lemma lem1304195 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term91 B2 n x m) = (term99 B2 n x m).
Proof. exact (TRANS (@lem1304187 B2 n x m) (@lem1304194 B2 n x m)). Qed.
Lemma lem1304196 (n : nat) (x : nadd) (m : nat) : (term100 n x m) = (term100 n x m).
Proof. exact (eq_refl (term100 n x m)). Qed.
Lemma lem1304197 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term101 B2 n x m) = (term102 B2 n x m).
Proof. exact (MK_COMB (@lem1304196 n x m) (@lem1304195 B2 n x m)). Qed.
Lemma lem1304199 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term69 m n p).
Proof. exact (EQ_MP (@lem1304117 m n p) (@lem1304116 m n p)). Qed.
Lemma lem1304200 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term102 B2 n x m) = (term103 B2 n x m).
Proof. exact (@lem1304199 (Nat.mul m n) (term96 B2 m x n) (term94 n x m)). Qed.
Lemma lem1304207 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term101 B2 n x m) = (term103 B2 n x m).
Proof. exact (TRANS (@lem1304197 B2 n x m) (@lem1304200 B2 n x m)). Qed.
Lemma lem1304208 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term103 B2 n x m) = (term101 B2 n x m).
Proof. exact (SYM (@lem1304207 B2 n x m)). Qed.
Lemma lem1304210 (a : nat) (c : nat) (b : nat) (d : nat) : (term59 a b c d) = (term60 a c b d).
Proof. exact (EQ_MP (@lem1304108 a c b d) (@lem0)). Qed.
Lemma lem1304211 (m : nat) (B2 : nat) (x : nadd) (n : nat) : (term96 B2 m x n) = (term104 m B2 x n).
Proof. exact (@lem1304210 B2 (dest_nadd x m) B2 (dest_nadd x n)). Qed.
Lemma lem1304212 (m : nat) (n : nat) : (term105 m n) = (term105 m n).
Proof. exact (eq_refl (term105 m n)). Qed.
Lemma lem1304213 (m : nat) (B2 : nat) (x : nadd) (n : nat) : (term106 B2 m x n) = (term107 m B2 x n).
Proof. exact (MK_COMB (@lem1304212 m n) (@lem1304211 m B2 x n)). Qed.
Lemma lem1304214 (B2 : nat) (m : nat) (x : nadd) (n : nat) : (term107 m B2 x n) = (term106 B2 m x n).
Proof. exact (SYM (@lem1304213 m B2 x n)). Qed.
Lemma lem1304216 (m : nat) (p : nat) (n : nat) (q : nat) : term48 m p n q.
Proof. exact (EQ_MP (@lem1304037 m p n q) (@lem1304036 m p n q)). Qed.
Lemma lem1304217 (m : nat) (B2 : nat) (x : nadd) (n : nat) : term108 m B2 x n.
Proof. exact (@lem1304216 m n (term109 B2 x m) (term109 B2 x n)). Qed.
Lemma lem1304218 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304219 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term110 N2 B2 x n.
Proof. exact (@lem1304218 N2 B2 x h1 n). Qed.
Lemma lem1304220 (N2 : nat) (B2 : nat) (x : nadd) (n : nat) : (term110 N2 B2 x n) = (term111 N2 B2 x n).
Proof. exact (eq_refl (term110 N2 B2 x n)). Qed.
Lemma lem1304221 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (EQ_MP (@lem1304220 N2 B2 x n) (@lem1304219 n N2 B2 x h1)). Qed.
Lemma lem1304222 (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : Peano.le N2 n.
Proof. exact (h1). Qed.
Lemma lem1304223 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : Peano.le N2 n) : term112 B2 x n.
Proof. exact (@lem1304221 n N2 B2 x h1 (@lem1304222 N2 n h2)). Qed.
Lemma lem1304224 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : term113 N2 B2 x n.
Proof. exact (fun h0 : term85 N2 B2 x => @lem1304223 B2 x N2 n h0 h1). Qed.
Lemma lem1304225 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304226 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : Peano.le N2 n) : term112 B2 x n.
Proof. exact (@lem1304224 B2 x N2 n h2 (@lem1304225 N2 B2 x h1)). Qed.
Lemma lem1304227 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (fun h0 : Peano.le N2 n => @lem1304226 B2 x N2 n h1 h0). Qed.
Lemma lem1304228 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (fun n : nat => @lem1304227 n N2 B2 x h1). Qed.
Lemma lem1304229 (N2 : nat) (B2 : nat) (x : nadd) : term114 N2 B2 x.
Proof. exact (fun h0 : term85 N2 B2 x => @lem1304228 N2 B2 x h0). Qed.
Lemma lem1304230 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (@lem1304229 N2 B2 x (@lem1304176 N2 B2 x h1)). Qed.
Lemma lem1304231 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term110 N2 B2 x n.
Proof. exact (@lem1304230 N2 B2 x h1 n). Qed.
Lemma lem1304232 (N2 : nat) (B2 : nat) (x : nadd) (n : nat) : (term110 N2 B2 x n) = (term111 N2 B2 x n).
Proof. exact (eq_refl (term110 N2 B2 x n)). Qed.
Lemma lem1304235 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (EQ_MP (@lem1304232 N2 B2 x n) (@lem1304231 n N2 B2 x h1)). Qed.
Lemma lem1304236 (m : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x m.
Proof. exact (@lem1304235 m N2 B2 x h1). Qed.
Lemma lem1304237 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304238 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term110 N2 B2 x n.
Proof. exact (@lem1304237 N2 B2 x h1 n). Qed.
Lemma lem1304239 (N2 : nat) (B2 : nat) (x : nadd) (n : nat) : (term110 N2 B2 x n) = (term111 N2 B2 x n).
Proof. exact (eq_refl (term110 N2 B2 x n)). Qed.
Lemma lem1304240 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (EQ_MP (@lem1304239 N2 B2 x n) (@lem1304238 n N2 B2 x h1)). Qed.
Lemma lem1304241 (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : Peano.le N2 n.
Proof. exact (h1). Qed.
Lemma lem1304242 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : Peano.le N2 n) : term112 B2 x n.
Proof. exact (@lem1304240 n N2 B2 x h1 (@lem1304241 N2 n h2)). Qed.
Lemma lem1304243 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : Peano.le N2 n) : term113 N2 B2 x n.
Proof. exact (fun h0 : term85 N2 B2 x => @lem1304242 B2 x N2 n h0 h1). Qed.
Lemma lem1304244 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (h1). Qed.
Lemma lem1304245 (B2 : nat) (x : nadd) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : Peano.le N2 n) : term112 B2 x n.
Proof. exact (@lem1304243 B2 x N2 n h2 (@lem1304244 N2 B2 x h1)). Qed.
Lemma lem1304246 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (fun h0 : Peano.le N2 n => @lem1304245 B2 x N2 n h1 h0). Qed.
Lemma lem1304247 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (fun n : nat => @lem1304246 n N2 B2 x h1). Qed.
Lemma lem1304248 (N2 : nat) (B2 : nat) (x : nadd) : term114 N2 B2 x.
Proof. exact (fun h0 : term85 N2 B2 x => @lem1304247 N2 B2 x h0). Qed.
Lemma lem1304249 (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term85 N2 B2 x.
Proof. exact (@lem1304248 N2 B2 x (@lem1304176 N2 B2 x h1)). Qed.
Lemma lem1304250 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term110 N2 B2 x n.
Proof. exact (@lem1304249 N2 B2 x h1 n). Qed.
Lemma lem1304251 (N2 : nat) (B2 : nat) (x : nadd) (n : nat) : (term110 N2 B2 x n) = (term111 N2 B2 x n).
Proof. exact (eq_refl (term110 N2 B2 x n)). Qed.
Lemma lem1304254 (n : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term85 N2 B2 x) : term111 N2 B2 x n.
Proof. exact (EQ_MP (@lem1304251 N2 B2 x n) (@lem1304250 n N2 B2 x h1)). Qed.
Lemma lem1304256 (b : nat) (c : nat) (a : nat) (d : nat) (e : nat) (f : nat) : (term28 a b c d e f) = (term38 b c a d e f).
Proof. exact (EQ_MP (@lem1304000 b c a d e f) (@lem0)). Qed.
Lemma lem1304257 (B2 : nat) (B1 : nat) (m : nat) (n : nat) : (term90 B1 B2 m n) = (term115 B2 B1 m n).
Proof. exact (@lem1304256 B2 B2 B1 m n (Nat.add m n)). Qed.
Lemma lem1304258 (B2 : nat) (n : nat) (x : nadd) (m : nat) : (term116 B2 n x m) = (term116 B2 n x m).
Proof. exact (eq_refl (term116 B2 n x m)). Qed.
Lemma lem1304259 (x : nadd) (B2 : nat) (B1 : nat) (m : nat) (n : nat) : (term117 x B1 B2 m n) = (term118 x B2 B1 m n).
Proof. exact (MK_COMB (@lem1304258 B2 n x m) (@lem1304257 B2 B1 m n)). Qed.
Lemma lem1304260 (x : nadd) (B1 : nat) (B2 : nat) (m : nat) (n : nat) : (term118 x B2 B1 m n) = (term117 x B1 B2 m n).
Proof. exact (SYM (@lem1304259 x B2 B1 m n)). Qed.
Lemma lem1304262 (m : nat) (n : nat) (p : nat) : (term22 n m p) = (term23 m n p).
Proof. exact (EQ_MP (@lem1303832 m n p) (@lem1303831 m n p)). Qed.
Lemma lem1304263 (B2 : nat) (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term118 x B2 B1 m n) = (term119 B2 x B1 m n).
Proof. exact (@lem1304262 (Nat.mul B2 B2) (term120 n x m) (term121 B1 m n)). Qed.
Lemma lem1304270 (x : nadd) (B2 : nat) (B1 : nat) (m : nat) (n : nat) : (term119 B2 x B1 m n) = (term118 x B2 B1 m n).
Proof. exact (SYM (@lem1304263 B2 x B1 m n)). Qed.
Lemma lem1304289 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term82 N1 x B1.
Proof. exact (h1). Qed.
Lemma lem1304290 (m : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term122 N1 x B1 m.
Proof. exact (@lem1304289 N1 x B1 h1 m). Qed.
Lemma lem1304291 (N1 : nat) (x : nadd) (B1 : nat) (m : nat) : (term122 N1 x B1 m) = (term123 N1 x B1 m).
Proof. exact (eq_refl (term122 N1 x B1 m)). Qed.
Lemma lem1304292 (m : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term123 N1 x B1 m.
Proof. exact (EQ_MP (@lem1304291 N1 x B1 m) (@lem1304290 m N1 x B1 h1)). Qed.
Lemma lem1304293 (m : nat) (n : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term124 N1 x B1 m n.
Proof. exact (@lem1304292 m N1 x B1 h1 n). Qed.
Lemma lem1304294 (N1 : nat) (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term124 N1 x B1 m n) = (term125 N1 x B1 m n).
Proof. exact (eq_refl (term124 N1 x B1 m n)). Qed.
Lemma lem1304295 (m : nat) (n : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term125 N1 x B1 m n.
Proof. exact (EQ_MP (@lem1304294 N1 x B1 m n) (@lem1304293 m n N1 x B1 h1)). Qed.
Lemma lem1304296 (m : nat) (N1 : nat) (n : nat) (h1 : term126 m N1 n) : term126 m N1 n.
Proof. exact (h1). Qed.
Lemma lem1304297 (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term126 m N1 n) : term127 x B1 m n.
Proof. exact (@lem1304295 m n N1 x B1 h1 (@lem1304296 m N1 n h2)). Qed.
Lemma lem1304298 (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (n : nat) (h1 : term126 m N1 n) : term128 N1 x B1 m n.
Proof. exact (fun h0 : term82 N1 x B1 => @lem1304297 x B1 m N1 n h0 h1). Qed.
Lemma lem1304299 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term82 N1 x B1.
Proof. exact (h1). Qed.
Lemma lem1304300 (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term126 m N1 n) : term127 x B1 m n.
Proof. exact (@lem1304298 x B1 m N1 n h2 (@lem1304299 N1 x B1 h1)). Qed.
Lemma lem1304301 (m : nat) (n : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term125 N1 x B1 m n.
Proof. exact (fun h0 : term126 m N1 n => @lem1304300 x B1 m N1 n h1 h0). Qed.
Lemma lem1304302 (m : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term123 N1 x B1 m.
Proof. exact (fun n : nat => @lem1304301 m n N1 x B1 h1). Qed.
Lemma lem1304303 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term82 N1 x B1.
Proof. exact (fun m : nat => @lem1304302 m N1 x B1 h1). Qed.
Lemma lem1304304 (N1 : nat) (x : nadd) (B1 : nat) : term129 N1 x B1.
Proof. exact (fun h0 : term82 N1 x B1 => @lem1304303 N1 x B1 h0). Qed.
Lemma lem1304305 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term82 N1 x B1.
Proof. exact (@lem1304304 N1 x B1 (@lem1304168 N1 x B1 h1)). Qed.
Lemma lem1304306 (m : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term122 N1 x B1 m.
Proof. exact (@lem1304305 N1 x B1 h1 m). Qed.
Lemma lem1304307 (N1 : nat) (x : nadd) (B1 : nat) (m : nat) : (term122 N1 x B1 m) = (term123 N1 x B1 m).
Proof. exact (eq_refl (term122 N1 x B1 m)). Qed.
Lemma lem1304308 (m : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term123 N1 x B1 m.
Proof. exact (EQ_MP (@lem1304307 N1 x B1 m) (@lem1304306 m N1 x B1 h1)). Qed.
Lemma lem1304309 (m : nat) (n : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term124 N1 x B1 m n.
Proof. exact (@lem1304308 m N1 x B1 h1 n). Qed.
Lemma lem1304310 (N1 : nat) (x : nadd) (B1 : nat) (m : nat) (n : nat) : (term124 N1 x B1 m n) = (term125 N1 x B1 m n).
Proof. exact (eq_refl (term124 N1 x B1 m n)). Qed.
Lemma lem1304313 (m : nat) (n : nat) (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term125 N1 x B1 m n.
Proof. exact (EQ_MP (@lem1304310 N1 x B1 m n) (@lem1304309 m n N1 x B1 h1)). Qed.
Lemma lem1304315 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303823 m p) (@lem1303822 m p)). Qed.
Lemma lem1304316 (N2 : nat) (m : nat) : term11 N2 m.
Proof. exact (@lem1304315 N2 m). Qed.
Lemma lem1304318 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303823 m p) (@lem1303822 m p)). Qed.
Lemma lem1304319 (N2 : nat) (n : nat) : term11 N2 n.
Proof. exact (@lem1304318 N2 n). Qed.
Lemma lem1304321 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303823 m p) (@lem1303822 m p)). Qed.
Lemma lem1304322 (N1 : nat) (m : nat) : term11 N1 m.
Proof. exact (@lem1304321 N1 m). Qed.
Lemma lem1304324 (m : nat) (p : nat) : term11 m p.
Proof. exact (EQ_MP (@lem1303823 m p) (@lem1303822 m p)). Qed.
Lemma lem1304325 (N1 : nat) (n : nat) : term11 N1 n.
Proof. exact (@lem1304324 N1 n). Qed.
Lemma lem1304326 (m : nat) : term130 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1304327 (m : nat) : (term130 m) = (term131 m).
Proof. exact (eq_refl (term130 m)). Qed.
Lemma lem1304328 (m : nat) : term131 m.
Proof. exact (EQ_MP (@lem1304327 m) (@lem1304326 m)). Qed.
Lemma lem1304329 (m : nat) (n : nat) : term132 m n.
Proof. exact (@lem1304328 m n). Qed.
Lemma lem1304330 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (eq_refl (term132 m n)). Qed.
Lemma lem1304331 (m : nat) (n : nat) : term133 m n.
Proof. exact (EQ_MP (@lem1304330 m n) (@lem1304329 m n)). Qed.
Lemma lem1304332 (m : nat) (n : nat) : (term133 m n) = ((term133 m n) = True).
Proof. exact (@lem7 (term133 m n)). Qed.
Lemma lem1304357 (N1 : nat) (N2 : nat) (m : nat) : (term87 N1 N2 m) = ((term87 N1 N2 m) = True).
Proof. exact (@lem7 (term87 N1 N2 m)). Qed.
Lemma lem1304364 (m : nat) (n : nat) : (term133 m n) = True.
Proof. exact (EQ_MP (@lem1304332 m n) (@lem1304331 m n)). Qed.
Lemma lem1304365 (N1 : nat) (N2 : nat) : (term133 N1 N2) = True.
Proof. exact (@lem1304364 N1 N2). Qed.
Lemma lem1304366 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1304367 (N1 : nat) (N2 : nat) : (term134 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1304366) (@lem1304365 N1 N2)). Qed.
Lemma lem1304369 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term87 N1 N2 m) = True.
Proof. exact (EQ_MP (@lem1304357 N1 N2 m) (@lem1304179 N1 N2 m h1)). Qed.
Lemma lem1304370 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term135 N1 N2 m) = (True /\ True).
Proof. exact (MK_COMB (@lem1304367 N1 N2) (@lem1304369 N1 N2 m h1)). Qed.
Lemma lem1304372 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1304373 : (True /\ True) = True.
Proof. exact (@lem1304372 True). Qed.
Lemma lem1304374 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term135 N1 N2 m) = True.
Proof. exact (TRANS (@lem1304370 N1 N2 m h1) (@lem1304373)). Qed.
Lemma lem1304375 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : True = (term135 N1 N2 m).
Proof. exact (SYM (@lem1304374 N1 N2 m h1)). Qed.
Lemma lem1304376 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : term135 N1 N2 m.
Proof. exact (EQ_MP (@lem1304375 N1 N2 m h1) (@lem0)). Qed.
Lemma lem1304377 (m : nat) : term130 m.
Proof. exact (@lem100562 m). Qed.
Lemma lem1304378 (m : nat) : (term130 m) = (term131 m).
Proof. exact (eq_refl (term130 m)). Qed.
Lemma lem1304379 (m : nat) : term131 m.
Proof. exact (EQ_MP (@lem1304378 m) (@lem1304377 m)). Qed.
Lemma lem1304380 (m : nat) (n : nat) : term132 m n.
Proof. exact (@lem1304379 m n). Qed.
Lemma lem1304381 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (eq_refl (term132 m n)). Qed.
Lemma lem1304382 (m : nat) (n : nat) : term133 m n.
Proof. exact (EQ_MP (@lem1304381 m n) (@lem1304380 m n)). Qed.
Lemma lem1304383 (m : nat) (n : nat) : (term133 m n) = ((term133 m n) = True).
Proof. exact (@lem7 (term133 m n)). Qed.
Lemma lem1304410 (N1 : nat) (N2 : nat) (n : nat) : (term87 N1 N2 n) = ((term87 N1 N2 n) = True).
Proof. exact (@lem7 (term87 N1 N2 n)). Qed.
Lemma lem1304415 (m : nat) (n : nat) : (term133 m n) = True.
Proof. exact (EQ_MP (@lem1304383 m n) (@lem1304382 m n)). Qed.
Lemma lem1304416 (N1 : nat) (N2 : nat) : (term133 N1 N2) = True.
Proof. exact (@lem1304415 N1 N2). Qed.
Lemma lem1304417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1304418 (N1 : nat) (N2 : nat) : (term134 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1304417) (@lem1304416 N1 N2)). Qed.
Lemma lem1304420 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term87 N1 N2 n) = True.
Proof. exact (EQ_MP (@lem1304410 N1 N2 n) (@lem1304178 N1 N2 n h1)). Qed.
Lemma lem1304421 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term135 N1 N2 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1304418 N1 N2) (@lem1304420 N1 N2 n h1)). Qed.
Lemma lem1304423 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1304424 : (True /\ True) = True.
Proof. exact (@lem1304423 True). Qed.
Lemma lem1304425 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term135 N1 N2 n) = True.
Proof. exact (TRANS (@lem1304421 N1 N2 n h1) (@lem1304424)). Qed.
Lemma lem1304426 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : True = (term135 N1 N2 n).
Proof. exact (SYM (@lem1304425 N1 N2 n h1)). Qed.
Lemma lem1304427 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : term135 N1 N2 n.
Proof. exact (EQ_MP (@lem1304426 N1 N2 n h1) (@lem0)). Qed.
Lemma lem1304436 (m : nat) : term136 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1304437 (m : nat) : (term136 m) = (term137 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1304438 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1304437 m) (@lem1304436 m)). Qed.
Lemma lem1304439 (m : nat) (n : nat) : term138 m n.
Proof. exact (@lem1304438 m n). Qed.
Lemma lem1304440 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem1304441 (m : nat) (n : nat) : term139 m n.
Proof. exact (EQ_MP (@lem1304440 m n) (@lem1304439 m n)). Qed.
Lemma lem1304442 (m : nat) (n : nat) : (term139 m n) = ((term139 m n) = True).
Proof. exact (@lem7 (term139 m n)). Qed.
Lemma lem1304459 (N1 : nat) (N2 : nat) (m : nat) : (term87 N1 N2 m) = ((term87 N1 N2 m) = True).
Proof. exact (@lem7 (term87 N1 N2 m)). Qed.
Lemma lem1304468 (m : nat) (n : nat) : (term139 m n) = True.
Proof. exact (EQ_MP (@lem1304442 m n) (@lem1304441 m n)). Qed.
Lemma lem1304469 (N1 : nat) (N2 : nat) : (term139 N1 N2) = True.
Proof. exact (@lem1304468 N1 N2). Qed.
Lemma lem1304470 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1304471 (N1 : nat) (N2 : nat) : (term140 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1304470) (@lem1304469 N1 N2)). Qed.
Lemma lem1304473 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term87 N1 N2 m) = True.
Proof. exact (EQ_MP (@lem1304459 N1 N2 m) (@lem1304179 N1 N2 m h1)). Qed.
Lemma lem1304474 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term141 N1 N2 m) = (True /\ True).
Proof. exact (MK_COMB (@lem1304471 N1 N2) (@lem1304473 N1 N2 m h1)). Qed.
Lemma lem1304476 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1304477 : (True /\ True) = True.
Proof. exact (@lem1304476 True). Qed.
Lemma lem1304478 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : (term141 N1 N2 m) = True.
Proof. exact (TRANS (@lem1304474 N1 N2 m h1) (@lem1304477)). Qed.
Lemma lem1304479 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : True = (term141 N1 N2 m).
Proof. exact (SYM (@lem1304478 N1 N2 m h1)). Qed.
Lemma lem1304480 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : term141 N1 N2 m.
Proof. exact (EQ_MP (@lem1304479 N1 N2 m h1) (@lem0)). Qed.
Lemma lem1304489 (m : nat) : term136 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1304490 (m : nat) : (term136 m) = (term137 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1304491 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1304490 m) (@lem1304489 m)). Qed.
Lemma lem1304492 (m : nat) (n : nat) : term138 m n.
Proof. exact (@lem1304491 m n). Qed.
Lemma lem1304493 (m : nat) (n : nat) : (term138 m n) = (term139 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem1304494 (m : nat) (n : nat) : term139 m n.
Proof. exact (EQ_MP (@lem1304493 m n) (@lem1304492 m n)). Qed.
Lemma lem1304495 (m : nat) (n : nat) : (term139 m n) = ((term139 m n) = True).
Proof. exact (@lem7 (term139 m n)). Qed.
Lemma lem1304514 (N1 : nat) (N2 : nat) (n : nat) : (term87 N1 N2 n) = ((term87 N1 N2 n) = True).
Proof. exact (@lem7 (term87 N1 N2 n)). Qed.
Lemma lem1304521 (m : nat) (n : nat) : (term139 m n) = True.
Proof. exact (EQ_MP (@lem1304495 m n) (@lem1304494 m n)). Qed.
Lemma lem1304522 (N1 : nat) (N2 : nat) : (term139 N1 N2) = True.
Proof. exact (@lem1304521 N1 N2). Qed.
Lemma lem1304523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1304524 (N1 : nat) (N2 : nat) : (term140 N1 N2) = (and True).
Proof. exact (MK_COMB (@lem1304523) (@lem1304522 N1 N2)). Qed.
Lemma lem1304526 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term87 N1 N2 n) = True.
Proof. exact (EQ_MP (@lem1304514 N1 N2 n) (@lem1304178 N1 N2 n h1)). Qed.
Lemma lem1304527 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term141 N1 N2 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1304524 N1 N2) (@lem1304526 N1 N2 n h1)). Qed.
Lemma lem1304529 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1304530 : (True /\ True) = True.
Proof. exact (@lem1304529 True). Qed.
Lemma lem1304531 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : (term141 N1 N2 n) = True.
Proof. exact (TRANS (@lem1304527 N1 N2 n h1) (@lem1304530)). Qed.
Lemma lem1304532 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : True = (term141 N1 N2 n).
Proof. exact (SYM (@lem1304531 N1 N2 n h1)). Qed.
Lemma lem1304533 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : term141 N1 N2 n.
Proof. exact (EQ_MP (@lem1304532 N1 N2 n h1) (@lem0)). Qed.
Lemma lem1304534 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : term9 N1 n.
Proof. exact (ex_intro (term10 N1 n) (Nat.add N1 N2) (@lem1304533 N1 N2 n h1)). Qed.
Lemma lem1304535 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : term9 N1 m.
Proof. exact (ex_intro (term10 N1 m) (Nat.add N1 N2) (@lem1304480 N1 N2 m h1)). Qed.
Lemma lem1304536 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : term9 N2 n.
Proof. exact (ex_intro (term10 N2 n) (Nat.add N1 N2) (@lem1304427 N1 N2 n h1)). Qed.
Lemma lem1304537 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : term9 N2 m.
Proof. exact (ex_intro (term10 N2 m) (Nat.add N1 N2) (@lem1304376 N1 N2 m h1)). Qed.
Lemma lem1304538 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : Peano.le N1 n.
Proof. exact (@lem1304325 N1 n (@lem1304534 N1 N2 n h1)). Qed.
Lemma lem1304539 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : Peano.le N1 m.
Proof. exact (@lem1304322 N1 m (@lem1304535 N1 N2 m h1)). Qed.
Lemma lem1304540 (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 n) : Peano.le N2 n.
Proof. exact (@lem1304319 N2 n (@lem1304536 N1 N2 n h1)). Qed.
Lemma lem1304541 (N1 : nat) (N2 : nat) (m : nat) (h1 : term87 N1 N2 m) : Peano.le N2 m.
Proof. exact (@lem1304316 N2 m (@lem1304537 N1 N2 m h1)). Qed.
Lemma lem1304542 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term87 N1 N2 m) (h2 : term87 N1 N2 n) : term126 m N1 n.
Proof. exact (conj (@lem1304539 N1 N2 m h1) (@lem1304538 N1 N2 n h2)). Qed.
Lemma lem1304543 (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term127 x B1 m n.
Proof. exact (@lem1304313 m n N1 x B1 h1 (@lem1304542 m N1 N2 n h2 h3)). Qed.
Lemma lem1304544 (B2 : nat) (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term119 B2 x B1 m n.
Proof. exact (or_intro2 ((Nat.mul B2 B2) = (NUMERAL 0)) (@lem1304543 x B1 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304545 (B2 : nat) (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term118 x B2 B1 m n.
Proof. exact (EQ_MP (@lem1304270 x B2 B1 m n) (@lem1304544 B2 x B1 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304546 (B2 : nat) (x : nadd) (B1 : nat) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term117 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1304260 x B1 B2 m n) (@lem1304545 B2 x B1 m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304547 (B2 : nat) (x : nadd) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 n) : term112 B2 x n.
Proof. exact (@lem1304254 n N2 B2 x h1 (@lem1304540 N1 N2 n h2)). Qed.
Lemma lem1304548 (B2 : nat) (x : nadd) (N1 : nat) (N2 : nat) (m : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) : term112 B2 x m.
Proof. exact (@lem1304236 m N2 B2 x h1 (@lem1304541 N1 N2 m h2)). Qed.
Lemma lem1304549 (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term142 m B2 x n.
Proof. exact (conj (@lem1304548 B2 x N1 N2 m h1 h2) (@lem1304547 B2 x N1 N2 n h1 h3)). Qed.
Lemma lem1304550 (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term107 m B2 x n.
Proof. exact (@lem1304217 m B2 x n (@lem1304549 B2 x m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304551 (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term106 B2 m x n.
Proof. exact (EQ_MP (@lem1304214 B2 m x n) (@lem1304550 B2 x m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304552 (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term103 B2 n x m.
Proof. exact (or_intro1 (@lem1304551 B2 x m N1 N2 n h1 h2 h3) ((term94 n x m) = (NUMERAL 0))). Qed.
Lemma lem1304553 (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term85 N2 B2 x) (h2 : term87 N1 N2 m) (h3 : term87 N1 N2 n) : term101 B2 n x m.
Proof. exact (EQ_MP (@lem1304208 B2 n x m) (@lem1304552 B2 x m N1 N2 n h1 h2 h3)). Qed.
Lemma lem1304554 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : term143 x B1 B2 m n.
Proof. exact (conj (@lem1304553 B2 x m N1 N2 n h2 h3 h4) (@lem1304546 B2 x B1 m N1 N2 n h1 h3 h4)). Qed.
Lemma lem1304555 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : term144 x B1 B2 m n.
Proof. exact (ex_intro (term145 x B1 B2 m n) (term91 B2 n x m) (@lem1304554 B1 B2 x m N1 N2 n h1 h2 h3 h4)). Qed.
Lemma lem1304556 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : term146 x B1 B2 m n.
Proof. exact (@lem1304182 x B1 B2 m n (@lem1304555 B1 B2 x m N1 N2 n h1 h2 h3 h4)). Qed.
Lemma lem1304557 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term86 m N1 N2 n) : term87 N1 N2 n.
Proof. exact (proj2 (@lem1304177 m N1 N2 n h1)). Qed.
Lemma lem1304558 (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term86 m N1 N2 n) : term87 N1 N2 m.
Proof. exact (proj1 (@lem1304177 m N1 N2 n h1)). Qed.
Lemma lem1304559 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : (term87 N1 N2 n) = (term146 x B1 B2 m n).
Proof. exact (prop_ext (fun h5 : term87 N1 N2 n => @lem1304556 B1 B2 x m N1 N2 n h1 h2 h3 h4) (fun h5 : term146 x B1 B2 m n => @lem1304178 N1 N2 n h4)). Qed.
Lemma lem1304560 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : term146 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1304559 B1 B2 x m N1 N2 n h1 h2 h3 h4) (@lem1304178 N1 N2 n h4)). Qed.
Lemma lem1304561 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : (term87 N1 N2 m) = (term146 x B1 B2 m n).
Proof. exact (prop_ext (fun h5 : term87 N1 N2 m => @lem1304560 B1 B2 x m N1 N2 n h1 h2 h3 h4) (fun h5 : term146 x B1 B2 m n => @lem1304179 N1 N2 m h3)). Qed.
Lemma lem1304562 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term87 N1 N2 m) (h4 : term87 N1 N2 n) : term146 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1304561 B1 B2 x m N1 N2 n h1 h2 h3 h4) (@lem1304179 N1 N2 m h3)). Qed.
Lemma lem1304563 (B1 : nat) (B2 : nat) (x : nadd) (n : nat) (N1 : nat) (N2 : nat) (m : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term86 m N1 N2 n) (h4 : term87 N1 N2 m) : (term87 N1 N2 n) = (term146 x B1 B2 m n).
Proof. exact (prop_ext (fun h5 : term87 N1 N2 n => @lem1304562 B1 B2 x m N1 N2 n h1 h2 h4 h5) (fun h5 : term146 x B1 B2 m n => @lem1304557 m N1 N2 n h3)). Qed.
Lemma lem1304564 (B1 : nat) (B2 : nat) (x : nadd) (n : nat) (N1 : nat) (N2 : nat) (m : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term86 m N1 N2 n) (h4 : term87 N1 N2 m) : term146 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1304563 B1 B2 x n N1 N2 m h1 h2 h3 h4) (@lem1304557 m N1 N2 n h3)). Qed.
Lemma lem1304565 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term86 m N1 N2 n) : (term87 N1 N2 m) = (term146 x B1 B2 m n).
Proof. exact (prop_ext (fun h4 : term87 N1 N2 m => @lem1304564 B1 B2 x n N1 N2 m h1 h2 h3 h4) (fun h4 : term146 x B1 B2 m n => @lem1304558 m N1 N2 n h3)). Qed.
Lemma lem1304566 (B1 : nat) (B2 : nat) (x : nadd) (m : nat) (N1 : nat) (N2 : nat) (n : nat) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) (h3 : term86 m N1 N2 n) : term146 x B1 B2 m n.
Proof. exact (EQ_MP (@lem1304565 B1 B2 x m N1 N2 n h1 h2 h3) (@lem1304558 m N1 N2 n h3)). Qed.
Lemma lem1304567 (m : nat) (n : nat) (N1 : nat) (B1 : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) : term147 N1 N2 x B1 B2 m n.
Proof. exact (fun h0 : term86 m N1 N2 n => @lem1304566 B1 B2 x m N1 N2 n h1 h2 h0). Qed.
Lemma lem1304572 (m : nat) (N1 : nat) (B1 : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) : term148 N1 N2 x B1 B2 m.
Proof. exact (fun n : nat => @lem1304567 m n N1 B1 N2 B2 x h1 h2). Qed.
Lemma lem1304577 (N1 : nat) (B1 : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) : term149 N1 N2 x B1 B2.
Proof. exact (fun m : nat => @lem1304572 m N1 B1 N2 B2 x h1 h2). Qed.
Lemma lem1304578 (N1 : nat) (B1 : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) : term150 x B1 B2.
Proof. exact (ex_intro (term151 x B1 B2) (Nat.add N1 N2) (@lem1304577 N1 B1 N2 B2 x h1 h2)). Qed.
Lemma lem1304579 (N1 : nat) (B1 : nat) (N2 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term85 N2 B2 x) : term152 x.
Proof. exact (ex_intro (term153 x) (term154 B1 B2) (@lem1304578 N1 B1 N2 B2 x h1 h2)). Qed.
Lemma lem1304580 (N1 : nat) (B1 : nat) (B2 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term84 B2 x) : term152 x.
Proof. exact (ex_elim (@lem1304175 B2 x h2) (fun N2 : nat => fun h0 : term155 B2 x N2 => @lem1304579 N1 B1 N2 B2 x h1 h0)). Qed.
Lemma lem1304581 (N1 : nat) (B1 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term83 x) : term152 x.
Proof. exact (ex_elim (@lem1304174 x h2) (fun B2 : nat => fun h0 : term156 x B2 => @lem1304580 N1 B1 B2 x h1 h0)). Qed.
Lemma lem1304582 (N1 : nat) (x : nadd) (B1 : nat) (h1 : term82 N1 x B1) : term157 x.
Proof. exact (fun h0 : term83 x => @lem1304581 N1 B1 x h1 h0). Qed.
Lemma lem1304583 (N1 : nat) (B1 : nat) (x : nadd) (h1 : term82 N1 x B1) (h2 : term79 x) : term152 x.
Proof. exact (@lem1304582 N1 x B1 h1 (@lem1304173 x h2)). Qed.
Lemma lem1304584 (B1 : nat) (x : nadd) (h1 : term81 x B1) (h2 : term79 x) : term152 x.
Proof. exact (ex_elim (@lem1304167 x B1 h1) (fun N1 : nat => fun h0 : term158 x B1 N1 => @lem1304583 N1 B1 x h0 h2)). Qed.
Lemma lem1304585 (x : nadd) (h1 : term80 x) (h2 : term79 x) : term152 x.
Proof. exact (ex_elim (@lem1304166 x h1) (fun B1 : nat => fun h0 : term159 x B1 => @lem1304584 B1 x h0 h2)). Qed.
Lemma lem1304586 (x : nadd) (h1 : term79 x) : term160 x.
Proof. exact (fun h0 : term80 x => @lem1304585 x h0 h1). Qed.
Lemma lem1304587 (x : nadd) (h1 : term79 x) : term152 x.
Proof. exact (@lem1304586 x h1 (@lem1304165 x h1)). Qed.
Lemma lem1304588 (x : nadd) : term161 x.
Proof. exact (fun h0 : term79 x => @lem1304587 x h0). Qed.
Lemma lem1304593 : term162.
Proof. exact (fun x : nadd => @lem1304588 x). Qed.
