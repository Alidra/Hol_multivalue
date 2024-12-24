Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1320277_term_abbrevs.
Require Import NADD_ADD_LID_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1317906_spec.
Require Import thm1317911_spec.
Require Import thm1318759_spec.
Require Import thm1318760_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1320224 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1320225 (x : nadd) : (term1 x) = ((term2 x) = (term0 x)).
Proof. exact (@lem1320224 (term3 x) x). Qed.
Lemma lem1320229 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1317911 x y) (@lem1317906 x y)). Qed.
Lemma lem1320230 (x : nadd) : (term2 x) = (term6 x).
Proof. exact (@lem1320229 term7 x). Qed.
Lemma lem1320232 (m : nat) : (term8 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1320233 : term9 = term10.
Proof. exact (@lem1320232 (NUMERAL 0)). Qed.
Lemma lem1320234 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1320235 : term11 = term12.
Proof. exact (MK_COMB (@lem1320234) (@lem1320233)). Qed.
Lemma lem1320236 (x : nadd) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1320237 (x : nadd) : (term6 x) = (term13 x).
Proof. exact (MK_COMB (@lem1320235) (@lem1320236 x)). Qed.
Lemma lem1320238 (x : nadd) : (term2 x) = (term13 x).
Proof. exact (TRANS (@lem1320230 x) (@lem1320237 x)). Qed.
Lemma lem1320239 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1320240 (x : nadd) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1320239) (@lem1320238 x)). Qed.
Lemma lem1320241 (x : nadd) : (term0 x) = (term0 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1320242 (x : nadd) : ((term2 x) = (term0 x)) = ((term13 x) = (term0 x)).
Proof. exact (MK_COMB (@lem1320240 x) (@lem1320241 x)). Qed.
Lemma lem1320245 (x : nadd) : (term1 x) = ((term13 x) = (term0 x)).
Proof. exact (TRANS (@lem1320225 x) (@lem1320242 x)). Qed.
Lemma lem1320246 : term16 = term17.
Proof. exact (fun_ext (fun x : nadd => @lem1320245 x)). Qed.
Lemma lem1320247 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320248 : term18 = term19.
Proof. exact (MK_COMB (@lem1320247) (@lem1320246)). Qed.
Lemma lem1320254 (P : hreal -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem1318760 P) (@lem1318759 P)). Qed.
Lemma lem1320255 : term22 = term23.
Proof. exact (@lem1320254 term24). Qed.
Lemma lem1320256 (x : nadd) : (term25 x) = ((term13 x) = (term0 x)).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1320257 : term26 = term17.
Proof. exact (fun_ext (fun x : nadd => @lem1320256 x)). Qed.
Lemma lem1320258 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1320259 : term22 = term19.
Proof. exact (MK_COMB (@lem1320258) (@lem1320257)). Qed.
Lemma lem1320260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1320261 : term27 = term28.
Proof. exact (MK_COMB (@lem1320260) (@lem1320259)). Qed.
Lemma lem1320262 (x : hreal) : (term29 x) = ((term30 x) = x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1320263 : term31 = term24.
Proof. exact (fun_ext (fun x : hreal => @lem1320262 x)). Qed.
Lemma lem1320264 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1320265 : term23 = term32.
Proof. exact (MK_COMB (@lem1320264) (@lem1320263)). Qed.
Lemma lem1320266 : (term22 = term23) = (term19 = term32).
Proof. exact (MK_COMB (@lem1320261) (@lem1320265)). Qed.
Lemma lem1320267 : term19 = term32.
Proof. exact (EQ_MP (@lem1320266) (@lem1320255)). Qed.
Lemma lem1320276 : term18 = term32.
Proof. exact (TRANS (@lem1320248) (@lem1320267)). Qed.
Lemma lem1320277 : term32.
Proof. exact (EQ_MP (@lem1320276) (@lem1274816)). Qed.
