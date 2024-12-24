Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1321192_term_abbrevs.
Require Import NADD_MUL_LINV_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318030_spec.
Require Import thm1318035_spec.
Require Import thm1318233_spec.
Require Import thm1318238_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1321114 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1321115 (x : nadd) : (term1 x) = ((term0 x) = term2).
Proof. exact (@lem1321114 x term3). Qed.
Lemma lem1321119 (m : nat) : (term4 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1321120 : term2 = term5.
Proof. exact (@lem1321119 (NUMERAL 0)). Qed.
Lemma lem1321121 (x : nadd) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1321122 (x : nadd) : ((term0 x) = term2) = ((term0 x) = term5).
Proof. exact (MK_COMB (@lem1321121 x) (@lem1321120)). Qed.
Lemma lem1321125 (x : nadd) : (term1 x) = ((term0 x) = term5).
Proof. exact (TRANS (@lem1321115 x) (@lem1321122 x)). Qed.
Lemma lem1321126 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1321127 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1321126) (@lem1321125 x)). Qed.
Lemma lem1321128 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1321129 (x : nadd) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1321128) (@lem1321127 x)). Qed.
Lemma lem1321131 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1321132 (x : nadd) : (term11 x) = ((term12 x) = term13).
Proof. exact (@lem1321131 (term14 x) term15). Qed.
Lemma lem1321136 (x : nadd) (y : nadd) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1318035 x y) (@lem1318030 x y)). Qed.
Lemma lem1321137 (x : nadd) : (term12 x) = (term18 x).
Proof. exact (@lem1321136 (nadd_inv x) x). Qed.
Lemma lem1321139 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1318238 x) (@lem1318233 x)). Qed.
Lemma lem1321140 : hreal_mul = hreal_mul.
Proof. exact (eq_refl hreal_mul). Qed.
Lemma lem1321141 (x : nadd) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1321140) (@lem1321139 x)). Qed.
Lemma lem1321142 (x : nadd) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1321143 (x : nadd) : (term18 x) = (term23 x).
Proof. exact (MK_COMB (@lem1321141 x) (@lem1321142 x)). Qed.
Lemma lem1321144 (x : nadd) : (term12 x) = (term23 x).
Proof. exact (TRANS (@lem1321137 x) (@lem1321143 x)). Qed.
Lemma lem1321145 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1321146 (x : nadd) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1321145) (@lem1321144 x)). Qed.
Lemma lem1321148 (m : nat) : (term4 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1321149 : term13 = term26.
Proof. exact (@lem1321148 term27). Qed.
Lemma lem1321150 (x : nadd) : ((term12 x) = term13) = ((term23 x) = term26).
Proof. exact (MK_COMB (@lem1321146 x) (@lem1321149)). Qed.
Lemma lem1321153 (x : nadd) : (term11 x) = ((term23 x) = term26).
Proof. exact (TRANS (@lem1321132 x) (@lem1321150 x)). Qed.
Lemma lem1321154 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1321129 x) (@lem1321153 x)). Qed.
Lemma lem1321157 : term30 = term31.
Proof. exact (fun_ext (fun x : nadd => @lem1321154 x)). Qed.
Lemma lem1321158 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321159 : term32 = term33.
Proof. exact (MK_COMB (@lem1321158) (@lem1321157)). Qed.
Lemma lem1321165 (P : hreal -> Prop) : (term34 P) = (term35 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1321166 : term36 = term37.
Proof. exact (@lem1321165 term38). Qed.
Lemma lem1321167 (x : nadd) : (term39 x) = (term29 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1321168 : term40 = term31.
Proof. exact (fun_ext (fun x : nadd => @lem1321167 x)). Qed.
Lemma lem1321169 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1321170 : term36 = term33.
Proof. exact (MK_COMB (@lem1321169) (@lem1321168)). Qed.
Lemma lem1321171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1321172 : term41 = term42.
Proof. exact (MK_COMB (@lem1321171) (@lem1321170)). Qed.
Lemma lem1321173 (x : hreal) : (term43 x) = (term44 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1321174 : term45 = term38.
Proof. exact (fun_ext (fun x : hreal => @lem1321173 x)). Qed.
Lemma lem1321175 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1321176 : term37 = term46.
Proof. exact (MK_COMB (@lem1321175) (@lem1321174)). Qed.
Lemma lem1321177 : (term36 = term37) = (term33 = term46).
Proof. exact (MK_COMB (@lem1321172) (@lem1321176)). Qed.
Lemma lem1321178 : term33 = term46.
Proof. exact (EQ_MP (@lem1321177) (@lem1321166)). Qed.
Lemma lem1321191 : term32 = term46.
Proof. exact (TRANS (@lem1321159) (@lem1321178)). Qed.
Lemma lem1321192 : term46.
Proof. exact (EQ_MP (@lem1321191) (@lem1308984)). Qed.
