Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_2_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_THM_spec.
Require Import BIT1_THM_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm86199_spec.
Lemma lem88011 : term0.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem88012 : term1.
Proof. exact (proj2 (@lem88011)). Qed.
Lemma lem88020 : term2.
Proof. exact (proj1 (@lem88012)). Qed.
Lemma lem88021 (m : nat) : term3 m.
Proof. exact (@lem88020 m). Qed.
Lemma lem88022 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem88023 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem88022 m) (@lem88021 m)). Qed.
Lemma lem88024 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem88023 m n). Qed.
Lemma lem88025 (m : nat) (n : nat) : (term5 m n) = ((term6 m n) = (term7 m n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem88027 : term8.
Proof. exact (proj1 (@lem88011)). Qed.
Lemma lem88028 (m : nat) : term9 m.
Proof. exact (@lem88027 m). Qed.
Lemma lem88029 (m : nat) : (term9 m) = ((term10 m) = m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem88031 : term11.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem88032 (n : nat) : term12 n.
Proof. exact (@lem88031 n). Qed.
Lemma lem88033 (n : nat) : (term12 n) = ((term13 n) = n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem88035 : term14.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem88036 : term15.
Proof. exact (proj2 (@lem88035)). Qed.
Lemma lem88037 : term16.
Proof. exact (proj2 (@lem88036)). Qed.
Lemma lem88038 : term17.
Proof. exact (proj2 (@lem88037)). Qed.
Lemma lem88039 : term18.
Proof. exact (proj2 (@lem88038)). Qed.
Lemma lem88040 (m : nat) : term19 m.
Proof. exact (@lem88039 m). Qed.
Lemma lem88041 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem88042 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem88041 m) (@lem88040 m)). Qed.
Lemma lem88043 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem88042 m n). Qed.
Lemma lem88044 (m : nat) (n : nat) : (term21 m n) = ((term22 m n) = (term23 m n)).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem88061 : term24.
Proof. exact (proj1 (@lem88035)). Qed.
Lemma lem88062 (m : nat) : term25 m.
Proof. exact (@lem88061 m). Qed.
Lemma lem88063 (m : nat) : (term25 m) = ((term26 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem88078 : term27.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem88079 (m : nat) : term28 m.
Proof. exact (@lem88078 m). Qed.
Lemma lem88080 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem88081 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem88080 m) (@lem88079 m)). Qed.
Lemma lem88082 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem88081 m n). Qed.
Lemma lem88083 (m : nat) (n : nat) : (term30 m n) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem88085 : term33.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem88086 (m : nat) : term34 m.
Proof. exact (@lem88085 m). Qed.
Lemma lem88087 (m : nat) : (term34 m) = ((term35 m) = term36).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem88089 (n : nat) : term37 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem88090 (n : nat) : (term37 n) = ((term38 n) = (term39 n)).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem88092 (n : nat) : term40 n.
Proof. exact (@lem80165 n). Qed.
Lemma lem88093 (n : nat) : (term40 n) = ((term41 n) = (term42 n)).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem88102 (n : nat) : (term41 n) = (term42 n).
Proof. exact (EQ_MP (@lem88093 n) (@lem88092 n)). Qed.
Lemma lem88103 : term43 = term44.
Proof. exact (@lem88102 (BIT1 0)). Qed.
Lemma lem88105 (n : nat) : (term38 n) = (term39 n).
Proof. exact (EQ_MP (@lem88090 n) (@lem88089 n)). Qed.
Lemma lem88106 : term36 = term45.
Proof. exact (@lem88105 0). Qed.
Lemma lem88108 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem88033 n) (@lem88032 n)). Qed.
Lemma lem88109 : term46 = (NUMERAL 0).
Proof. exact (@lem88108 (NUMERAL 0)). Qed.
Lemma lem88110 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem88111 : term45 = term47.
Proof. exact (MK_COMB (@lem88110) (@lem88109)). Qed.
Lemma lem88112 : term36 = term47.
Proof. exact (TRANS (@lem88106) (@lem88111)). Qed.
Lemma lem88113 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem88114 : term48 = term49.
Proof. exact (MK_COMB (@lem88113) (@lem88112)). Qed.
Lemma lem88116 (n : nat) : (term38 n) = (term39 n).
Proof. exact (EQ_MP (@lem88090 n) (@lem88089 n)). Qed.
Lemma lem88117 : term36 = term45.
Proof. exact (@lem88116 0). Qed.
Lemma lem88119 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem88033 n) (@lem88032 n)). Qed.
Lemma lem88120 : term46 = (NUMERAL 0).
Proof. exact (@lem88119 (NUMERAL 0)). Qed.
Lemma lem88121 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem88122 : term45 = term47.
Proof. exact (MK_COMB (@lem88121) (@lem88120)). Qed.
Lemma lem88123 : term36 = term47.
Proof. exact (TRANS (@lem88117) (@lem88122)). Qed.
Lemma lem88124 : term44 = term50.
Proof. exact (MK_COMB (@lem88114) (@lem88123)). Qed.
Lemma lem88126 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (EQ_MP (@lem88025 m n) (@lem88024 m n)). Qed.
Lemma lem88127 : term50 = term51.
Proof. exact (@lem88126 (NUMERAL 0) term47). Qed.
Lemma lem88129 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem88033 n) (@lem88032 n)). Qed.
Lemma lem88130 : term52 = term47.
Proof. exact (@lem88129 term47). Qed.
Lemma lem88131 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem88132 : term51 = term53.
Proof. exact (MK_COMB (@lem88131) (@lem88130)). Qed.
Lemma lem88133 : term50 = term53.
Proof. exact (TRANS (@lem88127) (@lem88132)). Qed.
Lemma lem88134 : term44 = term53.
Proof. exact (TRANS (@lem88124) (@lem88133)). Qed.
Lemma lem88135 : term43 = term53.
Proof. exact (TRANS (@lem88103) (@lem88134)). Qed.
Lemma lem88136 (n : nat) : (Nat.pow n) = (Nat.pow n).
Proof. exact (eq_refl (Nat.pow n)). Qed.
Lemma lem88137 (n : nat) : (term54 n) = (term55 n).
Proof. exact (MK_COMB (@lem88136 n) (@lem88135)). Qed.
Lemma lem88139 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem88083 m n) (@lem88082 m n)). Qed.
Lemma lem88140 (n : nat) : (term55 n) = (term56 n).
Proof. exact (@lem88139 n term47). Qed.
Lemma lem88142 (m : nat) (n : nat) : (term31 m n) = (term32 m n).
Proof. exact (EQ_MP (@lem88083 m n) (@lem88082 m n)). Qed.
Lemma lem88143 (n : nat) : (term57 n) = (term58 n).
Proof. exact (@lem88142 n (NUMERAL 0)). Qed.
Lemma lem88145 (m : nat) : (term35 m) = term36.
Proof. exact (EQ_MP (@lem88087 m) (@lem88086 m)). Qed.
Lemma lem88146 (n : nat) : (term35 n) = term36.
Proof. exact (@lem88145 n). Qed.
Lemma lem88148 (n : nat) : (term38 n) = (term39 n).
Proof. exact (EQ_MP (@lem88090 n) (@lem88089 n)). Qed.
Lemma lem88149 : term36 = term45.
Proof. exact (@lem88148 0). Qed.
Lemma lem88150 (n : nat) : (term35 n) = term45.
Proof. exact (TRANS (@lem88146 n) (@lem88149)). Qed.
Lemma lem88152 (n : nat) : (term13 n) = n.
Proof. exact (EQ_MP (@lem88033 n) (@lem88032 n)). Qed.
Lemma lem88153 : term46 = (NUMERAL 0).
Proof. exact (@lem88152 (NUMERAL 0)). Qed.
Lemma lem88154 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem88155 : term45 = term47.
Proof. exact (MK_COMB (@lem88154) (@lem88153)). Qed.
Lemma lem88156 (n : nat) : (term35 n) = term47.
Proof. exact (TRANS (@lem88150 n) (@lem88155)). Qed.
Lemma lem88157 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem88158 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem88157 n) (@lem88156 n)). Qed.
Lemma lem88160 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (EQ_MP (@lem88044 m n) (@lem88043 m n)). Qed.
Lemma lem88161 (n : nat) : (term59 n) = (term60 n).
Proof. exact (@lem88160 n (NUMERAL 0)). Qed.
Lemma lem88163 (m : nat) : (term26 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem88063 m) (@lem88062 m)). Qed.
Lemma lem88164 (n : nat) : (term26 n) = (NUMERAL 0).
Proof. exact (@lem88163 n). Qed.
Lemma lem88165 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem88166 (n : nat) : (term60 n) = (term10 n).
Proof. exact (MK_COMB (@lem88165 n) (@lem88164 n)). Qed.
Lemma lem88168 (m : nat) : (term10 m) = m.
Proof. exact (EQ_MP (@lem88029 m) (@lem88028 m)). Qed.
Lemma lem88169 (n : nat) : (term10 n) = n.
Proof. exact (@lem88168 n). Qed.
Lemma lem88170 (n : nat) : (term60 n) = n.
Proof. exact (TRANS (@lem88166 n) (@lem88169 n)). Qed.
Lemma lem88171 (n : nat) : (term59 n) = n.
Proof. exact (TRANS (@lem88161 n) (@lem88170 n)). Qed.
Lemma lem88172 (n : nat) : (term58 n) = n.
Proof. exact (TRANS (@lem88158 n) (@lem88171 n)). Qed.
Lemma lem88173 (n : nat) : (term57 n) = n.
Proof. exact (TRANS (@lem88143 n) (@lem88172 n)). Qed.
Lemma lem88174 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem88175 (n : nat) : (term56 n) = (Nat.mul n n).
Proof. exact (MK_COMB (@lem88174 n) (@lem88173 n)). Qed.
Lemma lem88176 (n : nat) : (term55 n) = (Nat.mul n n).
Proof. exact (TRANS (@lem88140 n) (@lem88175 n)). Qed.
Lemma lem88177 (n : nat) : (term54 n) = (Nat.mul n n).
Proof. exact (TRANS (@lem88137 n) (@lem88176 n)). Qed.
Lemma lem88178 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem88179 (n : nat) : (term61 n) = (term62 n).
Proof. exact (MK_COMB (@lem88178) (@lem88177 n)). Qed.
Lemma lem88180 (n : nat) : (Nat.mul n n) = (Nat.mul n n).
Proof. exact (eq_refl (Nat.mul n n)). Qed.
Lemma lem88181 (n : nat) : ((term54 n) = (Nat.mul n n)) = ((Nat.mul n n) = (Nat.mul n n)).
Proof. exact (MK_COMB (@lem88179 n) (@lem88180 n)). Qed.
Lemma lem88183 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem88184 (x : nat) : (x = x) = True.
Proof. exact (@lem88183 nat x). Qed.
Lemma lem88185 (n : nat) : ((Nat.mul n n) = (Nat.mul n n)) = True.
Proof. exact (@lem88184 (Nat.mul n n)). Qed.
Lemma lem88186 (n : nat) : ((term54 n) = (Nat.mul n n)) = True.
Proof. exact (TRANS (@lem88181 n) (@lem88185 n)). Qed.
Lemma lem88187 : term63 = term64.
Proof. exact (fun_ext (fun n : nat => @lem88186 n)). Qed.
Lemma lem88188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem88189 : term65 = term66.
Proof. exact (MK_COMB (@lem88188) (@lem88187)). Qed.
Lemma lem88191 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem88192 (t : Prop) : (term68 t) = t.
Proof. exact (@lem88191 nat t). Qed.
Lemma lem88193 : term66 = True.
Proof. exact (@lem88192 True). Qed.
Lemma lem88194 : term65 = True.
Proof. exact (TRANS (@lem88189) (@lem88193)). Qed.
Lemma lem88195 : True = term65.
Proof. exact (SYM (@lem88194)). Qed.
Lemma lem88196 : term65.
Proof. exact (EQ_MP (@lem88195) (@lem0)). Qed.
