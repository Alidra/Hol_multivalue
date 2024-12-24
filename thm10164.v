Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10164_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Lemma lem10094 (t : Prop) : term0 t.
Proof. exact (@lem9851 t). Qed.
Lemma lem10095 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem10096 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem10095 t) (@lem10094 t)). Qed.
Lemma lem10097 (t : Prop) (h1 : t = True) : t = True.
Proof. exact (h1). Qed.
Lemma lem10098 (t : Prop) (h1 : t = False) : t = False.
Proof. exact (h1). Qed.
Lemma lem10103 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem10104 (t : Prop) (h1 : t = True) : (term3 t) = term4.
Proof. exact (MK_COMB (@lem10103) (@lem10097 t h1)). Qed.
Lemma lem10105 : term4 = (term5 = True).
Proof. exact (eq_refl term4). Qed.
Lemma lem10106 (t : Prop) : (term6 t) = (term6 t).
Proof. exact (eq_refl (term6 t)). Qed.
Lemma lem10107 (t : Prop) : ((term3 t) = term4) = ((term3 t) = (term5 = True)).
Proof. exact (MK_COMB (@lem10106 t) (@lem10105)). Qed.
Lemma lem10108 (t : Prop) : (term3 t) = ((term7 t) = t).
Proof. exact (eq_refl (term3 t)). Qed.
Lemma lem10109 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10110 (t : Prop) : (term6 t) = (term8 t).
Proof. exact (MK_COMB (@lem10109) (@lem10108 t)). Qed.
Lemma lem10111 : (term5 = True) = (term5 = True).
Proof. exact (eq_refl (term5 = True)). Qed.
Lemma lem10112 (t : Prop) : ((term3 t) = (term5 = True)) = (((term7 t) = t) = (term5 = True)).
Proof. exact (MK_COMB (@lem10110 t) (@lem10111)). Qed.
Lemma lem10113 (t : Prop) : ((term3 t) = term4) = (((term7 t) = t) = (term5 = True)).
Proof. exact (TRANS (@lem10107 t) (@lem10112 t)). Qed.
Lemma lem10114 (t : Prop) (h1 : t = True) : ((term7 t) = t) = (term5 = True).
Proof. exact (EQ_MP (@lem10113 t) (@lem10104 t h1)). Qed.
Lemma lem10115 (t : Prop) (h1 : t = True) : (term5 = True) = ((term7 t) = t).
Proof. exact (SYM (@lem10114 t h1)). Qed.
Lemma lem10116 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem10117 (t : Prop) (h1 : t = False) : (term3 t) = term9.
Proof. exact (MK_COMB (@lem10116) (@lem10098 t h1)). Qed.
Lemma lem10118 : term9 = (term10 = False).
Proof. exact (eq_refl term9). Qed.
Lemma lem10119 (t : Prop) : (term6 t) = (term6 t).
Proof. exact (eq_refl (term6 t)). Qed.
Lemma lem10120 (t : Prop) : ((term3 t) = term9) = ((term3 t) = (term10 = False)).
Proof. exact (MK_COMB (@lem10119 t) (@lem10118)). Qed.
Lemma lem10121 (t : Prop) : (term3 t) = ((term7 t) = t).
Proof. exact (eq_refl (term3 t)). Qed.
Lemma lem10122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10123 (t : Prop) : (term6 t) = (term8 t).
Proof. exact (MK_COMB (@lem10122) (@lem10121 t)). Qed.
Lemma lem10124 : (term10 = False) = (term10 = False).
Proof. exact (eq_refl (term10 = False)). Qed.
Lemma lem10125 (t : Prop) : ((term3 t) = (term10 = False)) = (((term7 t) = t) = (term10 = False)).
Proof. exact (MK_COMB (@lem10123 t) (@lem10124)). Qed.
Lemma lem10126 (t : Prop) : ((term3 t) = term9) = (((term7 t) = t) = (term10 = False)).
Proof. exact (TRANS (@lem10120 t) (@lem10125 t)). Qed.
Lemma lem10127 (t : Prop) (h1 : t = False) : ((term7 t) = t) = (term10 = False).
Proof. exact (EQ_MP (@lem10126 t) (@lem10117 t h1)). Qed.
Lemma lem10128 (t : Prop) (h1 : t = False) : (term10 = False) = ((term7 t) = t).
Proof. exact (SYM (@lem10127 t h1)). Qed.
Lemma lem10130 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem10131 : (term5 = True) = term5.
Proof. exact (@lem10130 term5). Qed.
Lemma lem10133 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10135 : term5 = (~ False).
Proof. exact (MK_COMB (@lem10134) (@lem10133)). Qed.
Lemma lem10137 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10138 : term5 = True.
Proof. exact (TRANS (@lem10135) (@lem10137)). Qed.
Lemma lem10139 : (term5 = True) = True.
Proof. exact (TRANS (@lem10131) (@lem10138)). Qed.
Lemma lem10140 : True = (term5 = True).
Proof. exact (SYM (@lem10139)). Qed.
Lemma lem10141 : term5 = True.
Proof. exact (EQ_MP (@lem10140) (@lem0)). Qed.
Lemma lem10143 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem10144 : (term10 = False) = term11.
Proof. exact (@lem10143 term10). Qed.
Lemma lem10146 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10147 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10148 : term10 = (~ True).
Proof. exact (MK_COMB (@lem10147) (@lem10146)). Qed.
Lemma lem10150 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10151 : term10 = False.
Proof. exact (TRANS (@lem10148) (@lem10150)). Qed.
Lemma lem10152 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10153 : term11 = (~ False).
Proof. exact (MK_COMB (@lem10152) (@lem10151)). Qed.
Lemma lem10155 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10156 : term11 = True.
Proof. exact (TRANS (@lem10153) (@lem10155)). Qed.
Lemma lem10157 : (term10 = False) = True.
Proof. exact (TRANS (@lem10144) (@lem10156)). Qed.
Lemma lem10158 : True = (term10 = False).
Proof. exact (SYM (@lem10157)). Qed.
Lemma lem10159 : term10 = False.
Proof. exact (EQ_MP (@lem10158) (@lem0)). Qed.
Lemma lem10160 (t : Prop) (h1 : t = False) : (term7 t) = t.
Proof. exact (EQ_MP (@lem10128 t h1) (@lem10159)). Qed.
Lemma lem10161 (t : Prop) (h1 : t = True) : (term7 t) = t.
Proof. exact (EQ_MP (@lem10115 t h1) (@lem10141)). Qed.
Lemma lem10164 (t : Prop) : (term7 t) = t.
Proof. exact (or_elim (@lem10096 t) (fun h0 : t = True => @lem10161 t h0) (fun h0 : t = False => @lem10160 t h0)). Qed.
