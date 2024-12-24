Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338238_term_abbrevs.
Require Import TREAL_ADD_SYM_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1338105_spec.
Require Import thm1338106_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1338154 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1338155 (y : prod hreal hreal) (x : prod hreal hreal) : (term1 y x) = ((term2 x y) = (term2 y x)).
Proof. exact (@lem1338154 (treal_add x y) (treal_add y x)). Qed.
Lemma lem1338159 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term2 x1 y1) = (term3 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338160 (x : prod hreal hreal) (y : prod hreal hreal) : (term2 x y) = (term3 x y).
Proof. exact (@lem1338159 x y). Qed.
Lemma lem1338161 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1338162 (x : prod hreal hreal) (y : prod hreal hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1338161) (@lem1338160 x y)). Qed.
Lemma lem1338164 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term2 x1 y1) = (term3 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1338165 (y : prod hreal hreal) (x : prod hreal hreal) : (term2 y x) = (term3 y x).
Proof. exact (@lem1338164 y x). Qed.
Lemma lem1338166 (y : prod hreal hreal) (x : prod hreal hreal) : ((term2 x y) = (term2 y x)) = ((term3 x y) = (term3 y x)).
Proof. exact (MK_COMB (@lem1338162 x y) (@lem1338165 y x)). Qed.
Lemma lem1338169 (y : prod hreal hreal) (x : prod hreal hreal) : (term1 y x) = ((term3 x y) = (term3 y x)).
Proof. exact (TRANS (@lem1338155 y x) (@lem1338166 y x)). Qed.
Lemma lem1338170 (x : prod hreal hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338169 y x)). Qed.
Lemma lem1338171 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338172 (x : prod hreal hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1338171) (@lem1338170 x)). Qed.
Lemma lem1338178 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338179 (x : prod hreal hreal) : (term12 x) = (term13 x).
Proof. exact (@lem1338178 (term14 x)). Qed.
Lemma lem1338180 (y : prod hreal hreal) (x : prod hreal hreal) : (term15 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1338181 (x : prod hreal hreal) : (term16 x) = (term7 x).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1338180 y x)). Qed.
Lemma lem1338182 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338183 (x : prod hreal hreal) : (term12 x) = (term9 x).
Proof. exact (MK_COMB (@lem1338182) (@lem1338181 x)). Qed.
Lemma lem1338184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338185 (x : prod hreal hreal) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1338184) (@lem1338183 x)). Qed.
Lemma lem1338186 (y : real) (x : prod hreal hreal) : (term19 x y) = ((term20 x y) = (term21 y x)).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1338187 (x : prod hreal hreal) : (term22 x) = (term14 x).
Proof. exact (fun_ext (fun y : real => @lem1338186 y x)). Qed.
Lemma lem1338188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338189 (x : prod hreal hreal) : (term13 x) = (term23 x).
Proof. exact (MK_COMB (@lem1338188) (@lem1338187 x)). Qed.
Lemma lem1338190 (x : prod hreal hreal) : ((term12 x) = (term13 x)) = ((term9 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1338185 x) (@lem1338189 x)). Qed.
Lemma lem1338191 (x : prod hreal hreal) : (term9 x) = (term23 x).
Proof. exact (EQ_MP (@lem1338190 x) (@lem1338179 x)). Qed.
Lemma lem1338200 (x : prod hreal hreal) : (term8 x) = (term23 x).
Proof. exact (TRANS (@lem1338172 x) (@lem1338191 x)). Qed.
Lemma lem1338201 : term24 = term25.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338200 x)). Qed.
Lemma lem1338202 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338203 : term26 = term27.
Proof. exact (MK_COMB (@lem1338202) (@lem1338201)). Qed.
Lemma lem1338209 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem1338106 P) (@lem1338105 P)). Qed.
Lemma lem1338210 : term28 = term29.
Proof. exact (@lem1338209 term30). Qed.
Lemma lem1338211 (x : prod hreal hreal) : (term31 x) = (term23 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1338212 : term32 = term25.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1338211 x)). Qed.
Lemma lem1338213 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1338214 : term28 = term27.
Proof. exact (MK_COMB (@lem1338213) (@lem1338212)). Qed.
Lemma lem1338215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338216 : term33 = term34.
Proof. exact (MK_COMB (@lem1338215) (@lem1338214)). Qed.
Lemma lem1338217 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1338218 : term37 = term30.
Proof. exact (fun_ext (fun x : real => @lem1338217 x)). Qed.
Lemma lem1338219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1338220 : term29 = term38.
Proof. exact (MK_COMB (@lem1338219) (@lem1338218)). Qed.
Lemma lem1338221 : (term28 = term29) = (term27 = term38).
Proof. exact (MK_COMB (@lem1338216) (@lem1338220)). Qed.
Lemma lem1338222 : term27 = term38.
Proof. exact (EQ_MP (@lem1338221) (@lem1338210)). Qed.
Lemma lem1338237 : term26 = term38.
Proof. exact (TRANS (@lem1338203) (@lem1338222)). Qed.
Lemma lem1338238 : term38.
Proof. exact (EQ_MP (@lem1338237) (@lem1327796)). Qed.
