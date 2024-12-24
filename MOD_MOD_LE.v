Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MOD_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import DIVISION_spec.
Require Import LTE_TRANS_spec.
Require Import MOD_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm19490_spec.
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
Require Import thm69_spec.
Lemma lem183011 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem183012 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem183013 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem183012 t1) (@lem183011 t1)). Qed.
Lemma lem183014 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem183013 t1 t2). Qed.
Lemma lem183015 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem183016 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem183015 t1 t2) (@lem183014 t1 t2)). Qed.
Lemma lem183017 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem183016 t1 t2 t3). Qed.
Lemma lem183018 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem183019 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem183018 t1 t2 t3) (@lem183017 t1 t2 t3)). Qed.
Lemma lem183020 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem183019 t1 t2 t3)). Qed.
Lemma lem183021 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem183022 (m : nat) (h1 : term7) : term8 m.
Proof. exact (@lem183021 h1 m). Qed.
Lemma lem183023 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem183024 (m : nat) (h1 : term7) : term9 m.
Proof. exact (EQ_MP (@lem183023 m) (@lem183022 m h1)). Qed.
Lemma lem183025 (m : nat) (n : nat) (h1 : term7) : term10 m n.
Proof. exact (@lem183024 m h1 n). Qed.
Lemma lem183026 (n : nat) (m : nat) : (term10 m n) = (term11 n m).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem183027 (n : nat) (m : nat) (h1 : term7) : term11 n m.
Proof. exact (EQ_MP (@lem183026 n m) (@lem183025 m n h1)). Qed.
Lemma lem183028 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem183029 (m : nat) (n : nat) (h1 : term7) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem183027 n m h1 (@lem183028 m n h2)). Qed.
Lemma lem183030 (m : nat) (n : nat) (h1 : Peano.lt m n) : term12 n m.
Proof. exact (fun h0 : term7 => @lem183029 m n h0 h1). Qed.
Lemma lem183031 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem183032 (m : nat) (n : nat) (h1 : term7) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem183030 m n h2 (@lem183031 h1)). Qed.
Lemma lem183033 (n : nat) (m : nat) (h1 : term7) : term11 n m.
Proof. exact (fun h0 : Peano.lt m n => @lem183032 m n h1 h0). Qed.
Lemma lem183034 (n : nat) (h1 : term7) : term13 n.
Proof. exact (fun m : nat => @lem183033 n m h1). Qed.
Lemma lem183035 (h1 : term7) : term14.
Proof. exact (fun n : nat => @lem183034 n h1). Qed.
Lemma lem183036 : term15.
Proof. exact (fun h0 : term7 => @lem183035 h0). Qed.
Lemma lem183037 : term14.
Proof. exact (@lem183036 (@lem170673)). Qed.
Lemma lem183038 (n : nat) : term16 n.
Proof. exact (@lem183037 n). Qed.
Lemma lem183039 (n : nat) : (term16 n) = (term13 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem183040 (n : nat) : term13 n.
Proof. exact (EQ_MP (@lem183039 n) (@lem183038 n)). Qed.
Lemma lem183041 (n : nat) (m : nat) : term17 n m.
Proof. exact (@lem183040 n m). Qed.
Lemma lem183042 (n : nat) (m : nat) : (term17 n m) = (term11 n m).
Proof. exact (eq_refl (term17 n m)). Qed.
Lemma lem183044 (n : nat) (p : nat) (h1 : term18 n p) : term18 n p.
Proof. exact (h1). Qed.
Lemma lem183045 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183046 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183048 (n : nat) (m : nat) : term11 n m.
Proof. exact (EQ_MP (@lem183042 n m) (@lem183041 n m)). Qed.
Lemma lem183049 (p : nat) (m : nat) (n : nat) : term20 p m n.
Proof. exact (@lem183048 p (Nat.modulo m n)). Qed.
Lemma lem183051 (p : Prop) : p = (term21 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem183052 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (@lem183051 (term22 m n p)). Qed.
Lemma lem183053 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (term22 m n p).
Proof. exact (SYM (@lem183052 m n p)). Qed.
Lemma lem183054 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem183057 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem183058 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (fun h0 : term25 m n p => @lem183057 m n p h0). Qed.
Lemma lem183059 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (h1). Qed.
Lemma lem183060 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term25 m n p.
Proof. exact (h1). Qed.
Lemma lem183061 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : term26 m n p) : term25 m n p.
Proof. exact (@lem183059 m n p h2 (@lem183060 m n p h1)). Qed.
Lemma lem183062 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) : term27 m n p.
Proof. exact (fun h0 : term26 m n p => @lem183061 m n p h1 h0). Qed.
Lemma lem183063 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (h1). Qed.
Lemma lem183064 (m : nat) (n : nat) (p : nat) (h1 : term25 m n p) (h2 : term26 m n p) : term25 m n p.
Proof. exact (@lem183062 m n p h1 (@lem183063 m n p h2)). Qed.
Lemma lem183065 (m : nat) (n : nat) (p : nat) (h1 : term26 m n p) : term26 m n p.
Proof. exact (fun h0 : term25 m n p => @lem183064 m n p h0 h1). Qed.
Lemma lem183066 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (fun h0 : term26 m n p => @lem183065 m n p h0). Qed.
Lemma lem183069 (m : nat) (n : nat) (p : nat) : term26 m n p.
Proof. exact (@lem183066 m n p (@lem183058 m n p)). Qed.
Lemma lem183107 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem183108 : term29 = term30.
Proof. exact (@lem183107 term31). Qed.
Lemma lem183121 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem183122 : term33 = term34.
Proof. exact (MK_COMB (@lem183121) (@lem183108)). Qed.
Lemma lem183125 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (term35 m n p).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem183126 (m : nat) (n : nat) (p : nat) : (term36 m n p) = (term37 m n p).
Proof. exact (MK_COMB (@lem183125 m n p) (@lem183122)). Qed.
Lemma lem183129 (n : nat) (p : nat) : (term38 n p) = (term38 n p).
Proof. exact (eq_refl (term38 n p)). Qed.
Lemma lem183130 (m : nat) (n : nat) (p : nat) : (term39 m n p) = (term40 m n p).
Proof. exact (MK_COMB (@lem183129 n p) (@lem183126 m n p)). Qed.
Lemma lem183133 (n : nat) : (term41 n) = (term41 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem183134 (m : nat) (n : nat) (p : nat) : (term25 m n p) = (term42 m n p).
Proof. exact (MK_COMB (@lem183133 n) (@lem183130 m n p)). Qed.
Lemma lem183137 (n : nat) (p : nat) : (term43 n p) = (term44 n p).
Proof. exact (fun_ext (fun m : nat => @lem183134 m n p)). Qed.
Lemma lem183138 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183139 (n : nat) (p : nat) : (term45 n p) = (term46 n p).
Proof. exact (MK_COMB (@lem183138) (@lem183137 n p)). Qed.
Lemma lem183144 (p : nat) : (term47 p) = (term48 p).
Proof. exact (fun_ext (fun n : nat => @lem183139 n p)). Qed.
Lemma lem183145 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183146 (p : nat) : (term49 p) = (term50 p).
Proof. exact (MK_COMB (@lem183145) (@lem183144 p)). Qed.
Lemma lem183151 : term51 = term52.
Proof. exact (fun_ext (fun p : nat => @lem183146 p)). Qed.
Lemma lem183152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183161 : term53 = term54.
Proof. exact (MK_COMB (@lem183152) (@lem183151)). Qed.
Lemma lem183172 (m : nat) (n : nat) : (term55 m n) = (term55 m n).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem183173 (m : nat) : (term56 m) = (term56 m).
Proof. exact (fun_ext (fun n : nat => @lem183172 m n)). Qed.
Lemma lem183174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183175 (m : nat) : (term57 m) = (term57 m).
Proof. exact (MK_COMB (@lem183174) (@lem183173 m)). Qed.
Lemma lem183176 : term58 = term58.
Proof. exact (fun_ext (fun m : nat => @lem183175 m)). Qed.
Lemma lem183177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183178 : term31 = term31.
Proof. exact (MK_COMB (@lem183177) (@lem183176)). Qed.
Lemma lem183179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem183180 : term30 = term30.
Proof. exact (MK_COMB (@lem183179) (@lem183178)). Qed.
Lemma lem183189 (n : nat) (m : nat) (p : nat) : (term59 n m p) = (term59 n m p).
Proof. exact (eq_refl (term59 n m p)). Qed.
Lemma lem183190 (n : nat) (m : nat) : (term60 n m) = (term60 n m).
Proof. exact (fun_ext (fun p : nat => @lem183189 n m p)). Qed.
Lemma lem183191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183192 (n : nat) (m : nat) : (term61 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem183191) (@lem183190 n m)). Qed.
Lemma lem183193 (m : nat) : (term62 m) = (term62 m).
Proof. exact (fun_ext (fun n : nat => @lem183192 n m)). Qed.
Lemma lem183194 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183195 (m : nat) : (term63 m) = (term63 m).
Proof. exact (MK_COMB (@lem183194) (@lem183193 m)). Qed.
Lemma lem183196 : term64 = term64.
Proof. exact (fun_ext (fun m : nat => @lem183195 m)). Qed.
Lemma lem183197 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183198 : term65 = term65.
Proof. exact (MK_COMB (@lem183197) (@lem183196)). Qed.
Lemma lem183199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem183200 : term32 = term32.
Proof. exact (MK_COMB (@lem183199) (@lem183198)). Qed.
Lemma lem183201 : term34 = term34.
Proof. exact (MK_COMB (@lem183200) (@lem183180)). Qed.
Lemma lem183206 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (term35 m n p).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem183207 (m : nat) (n : nat) (p : nat) : (term37 m n p) = (term37 m n p).
Proof. exact (MK_COMB (@lem183206 m n p) (@lem183201)). Qed.
Lemma lem183210 (n : nat) (p : nat) : (term38 n p) = (term38 n p).
Proof. exact (eq_refl (term38 n p)). Qed.
Lemma lem183211 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (term40 m n p).
Proof. exact (MK_COMB (@lem183210 n p) (@lem183207 m n p)). Qed.
Lemma lem183216 (n : nat) : (term41 n) = (term41 n).
Proof. exact (eq_refl (term41 n)). Qed.
Lemma lem183217 (m : nat) (n : nat) (p : nat) : (term42 m n p) = (term42 m n p).
Proof. exact (MK_COMB (@lem183216 n) (@lem183211 m n p)). Qed.
Lemma lem183218 (n : nat) (p : nat) : (term44 n p) = (term44 n p).
Proof. exact (fun_ext (fun m : nat => @lem183217 m n p)). Qed.
Lemma lem183219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183220 (n : nat) (p : nat) : (term46 n p) = (term46 n p).
Proof. exact (MK_COMB (@lem183219) (@lem183218 n p)). Qed.
Lemma lem183221 (p : nat) : (term48 p) = (term48 p).
Proof. exact (fun_ext (fun n : nat => @lem183220 n p)). Qed.
Lemma lem183222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183223 (p : nat) : (term50 p) = (term50 p).
Proof. exact (MK_COMB (@lem183222) (@lem183221 p)). Qed.
Lemma lem183224 : term52 = term52.
Proof. exact (fun_ext (fun p : nat => @lem183223 p)). Qed.
Lemma lem183225 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183226 : term54 = term54.
Proof. exact (MK_COMB (@lem183225) (@lem183224)). Qed.
Lemma lem183293 : term53 = term54.
Proof. exact (TRANS (@lem183161) (@lem183226)). Qed.
Lemma lem183294 : term54 = term53.
Proof. exact (SYM (@lem183293)). Qed.
Lemma lem183298 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem183299 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem183305 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183311 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183317 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem183324 (m : nat) (n : nat) (p : nat) : (term66 m n p) = (term67 m n p).
Proof. exact (@lem17045 (Peano.lt m n) (Peano.le n p)). Qed.
Lemma lem183325 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem183326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem183327 (m : nat) (n : nat) (p : nat) : (term68 m n p) = (term69 m n p).
Proof. exact (MK_COMB (@lem183326) (@lem183324 m n p)). Qed.
Lemma lem183328 (n : nat) (m : nat) (p : nat) : (term70 n m p) = (term71 n m p).
Proof. exact (MK_COMB (@lem183327 m n p) (@lem183325 m p)). Qed.
Lemma lem183329 (n : nat) (m : nat) (p : nat) : (term59 n m p) = (term70 n m p).
Proof. exact (@lem17265 (term72 m n p) (Peano.lt m p)). Qed.
Lemma lem183330 (n : nat) (m : nat) (p : nat) : (term59 n m p) = (term71 n m p).
Proof. exact (TRANS (@lem183329 n m p) (@lem183328 n m p)). Qed.
Lemma lem183331 (n : nat) (m : nat) : (term60 n m) = (term73 n m).
Proof. exact (fun_ext (fun p : nat => @lem183330 n m p)). Qed.
Lemma lem183332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183333 (n : nat) (m : nat) : (term61 n m) = (term74 n m).
Proof. exact (MK_COMB (@lem183332) (@lem183331 n m)). Qed.
Lemma lem183334 (m : nat) : (term62 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem183333 n m)). Qed.
Lemma lem183335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183336 (m : nat) : (term63 m) = (term76 m).
Proof. exact (MK_COMB (@lem183335) (@lem183334 m)). Qed.
Lemma lem183337 : term64 = term77.
Proof. exact (fun_ext (fun m : nat => @lem183336 m)). Qed.
Lemma lem183338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183399 : term65 = term78.
Proof. exact (MK_COMB (@lem183338) (@lem183337)). Qed.
Lemma lem183400 (h1 : term65) : term78.
Proof. exact (EQ_MP (@lem183399) (@lem183298 h1)). Qed.
Lemma lem183403 (n : nat) : (term79 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem183408 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (eq_refl (term80 m n)). Qed.
Lemma lem183409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem183410 (n : nat) : (term81 n) = (term82 n).
Proof. exact (MK_COMB (@lem183409) (@lem183403 n)). Qed.
Lemma lem183411 (m : nat) (n : nat) : (term83 m n) = (term84 m n).
Proof. exact (MK_COMB (@lem183410 n) (@lem183408 m n)). Qed.
Lemma lem183412 (m : nat) (n : nat) : (term55 m n) = (term83 m n).
Proof. exact (@lem17265 (term19 n) (term80 m n)). Qed.
Lemma lem183413 (m : nat) (n : nat) : (term55 m n) = (term84 m n).
Proof. exact (TRANS (@lem183412 m n) (@lem183411 m n)). Qed.
Lemma lem183414 (m : nat) : (term56 m) = (term85 m).
Proof. exact (fun_ext (fun n : nat => @lem183413 m n)). Qed.
Lemma lem183415 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183416 (m : nat) : (term57 m) = (term86 m).
Proof. exact (MK_COMB (@lem183415) (@lem183414 m)). Qed.
Lemma lem183417 : term58 = term87.
Proof. exact (fun_ext (fun m : nat => @lem183416 m)). Qed.
Lemma lem183418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183475 : term31 = term88.
Proof. exact (MK_COMB (@lem183418) (@lem183417)). Qed.
Lemma lem183476 (h1 : term31) : term88.
Proof. exact (EQ_MP (@lem183475) (@lem183299 h1)). Qed.
Lemma lem183486 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183492 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183504 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem183529 (n : nat) (m : nat) (p : nat) : (term71 n m p) = (term71 n m p).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem183530 (n : nat) (m : nat) : (term73 n m) = (term73 n m).
Proof. exact (fun_ext (fun p : nat => @lem183529 n m p)). Qed.
Lemma lem183531 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183532 (n : nat) (m : nat) : (term74 n m) = (term74 n m).
Proof. exact (MK_COMB (@lem183531) (@lem183530 n m)). Qed.
Lemma lem183533 (m : nat) : (term75 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem183532 n m)). Qed.
Lemma lem183534 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183535 (m : nat) : (term76 m) = (term76 m).
Proof. exact (MK_COMB (@lem183534) (@lem183533 m)). Qed.
Lemma lem183536 : term77 = term77.
Proof. exact (fun_ext (fun m : nat => @lem183535 m)). Qed.
Lemma lem183537 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183538 : term78 = term78.
Proof. exact (MK_COMB (@lem183537) (@lem183536)). Qed.
Lemma lem183539 (h1 : term65) : term78.
Proof. exact (EQ_MP (@lem183538) (@lem183400 h1)). Qed.
Lemma lem183582 (m : nat) (n : nat) : (term84 m n) = (term84 m n).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem183583 (m : nat) : (term85 m) = (term85 m).
Proof. exact (fun_ext (fun n : nat => @lem183582 m n)). Qed.
Lemma lem183584 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183585 (m : nat) : (term86 m) = (term86 m).
Proof. exact (MK_COMB (@lem183584) (@lem183583 m)). Qed.
Lemma lem183586 : term87 = term87.
Proof. exact (fun_ext (fun m : nat => @lem183585 m)). Qed.
Lemma lem183587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183588 : term88 = term88.
Proof. exact (MK_COMB (@lem183587) (@lem183586)). Qed.
Lemma lem183589 (h1 : term31) : term88.
Proof. exact (EQ_MP (@lem183588) (@lem183476 h1)). Qed.
Lemma lem183593 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183597 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183601 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem183615 (n : nat) (m : nat) (p : nat) : (term71 n m p) = (term71 n m p).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem183616 (n : nat) (m : nat) : (term73 n m) = (term73 n m).
Proof. exact (fun_ext (fun p : nat => @lem183615 n m p)). Qed.
Lemma lem183617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183618 (n : nat) (m : nat) : (term74 n m) = (term74 n m).
Proof. exact (MK_COMB (@lem183617) (@lem183616 n m)). Qed.
Lemma lem183619 (m : nat) : (term75 m) = (term75 m).
Proof. exact (fun_ext (fun n : nat => @lem183618 n m)). Qed.
Lemma lem183620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183621 (m : nat) : (term76 m) = (term76 m).
Proof. exact (MK_COMB (@lem183620) (@lem183619 m)). Qed.
Lemma lem183622 : term77 = term77.
Proof. exact (fun_ext (fun m : nat => @lem183621 m)). Qed.
Lemma lem183623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183625 : term78 = term78.
Proof. exact (MK_COMB (@lem183623) (@lem183622)). Qed.
Lemma lem183626 (h1 : term65) : term78.
Proof. exact (EQ_MP (@lem183625) (@lem183539 h1)). Qed.
Lemma lem183644 (m : nat) (n : nat) : (term84 m n) = (term89 m n).
Proof. exact (@lem19490 (m = (term90 m n)) (n = (NUMERAL 0)) (term91 m n)). Qed.
Lemma lem183645 (m : nat) : (term85 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem183644 m n)). Qed.
Lemma lem183646 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183647 (m : nat) : (term86 m) = (term93 m).
Proof. exact (MK_COMB (@lem183646) (@lem183645 m)). Qed.
Lemma lem183648 : term87 = term94.
Proof. exact (fun_ext (fun m : nat => @lem183647 m)). Qed.
Lemma lem183649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem183651 : term88 = term95.
Proof. exact (MK_COMB (@lem183649) (@lem183648)). Qed.
Lemma lem183652 (h1 : term31) : term95.
Proof. exact (EQ_MP (@lem183651) (@lem183589 h1)). Qed.
Lemma lem183653 (_3740 : nat) (h1 : term65) : term96 _3740.
Proof. exact (@lem183626 h1 _3740). Qed.
Lemma lem183654 (_3740 : nat) : (term96 _3740) = (term76 _3740).
Proof. exact (eq_refl (term96 _3740)). Qed.
Lemma lem183655 (_3740 : nat) (h1 : term65) : term76 _3740.
Proof. exact (EQ_MP (@lem183654 _3740) (@lem183653 _3740 h1)). Qed.
Lemma lem183656 (_3740 : nat) (_3741 : nat) (h1 : term65) : term97 _3740 _3741.
Proof. exact (@lem183655 _3740 h1 _3741). Qed.
Lemma lem183657 (_3741 : nat) (_3740 : nat) : (term97 _3740 _3741) = (term74 _3741 _3740).
Proof. exact (eq_refl (term97 _3740 _3741)). Qed.
Lemma lem183658 (_3741 : nat) (_3740 : nat) (h1 : term65) : term74 _3741 _3740.
Proof. exact (EQ_MP (@lem183657 _3741 _3740) (@lem183656 _3740 _3741 h1)). Qed.
Lemma lem183659 (_3741 : nat) (_3740 : nat) (_3742 : nat) (h1 : term65) : term98 _3741 _3740 _3742.
Proof. exact (@lem183658 _3741 _3740 h1 _3742). Qed.
Lemma lem183660 (_3741 : nat) (_3740 : nat) (_3742 : nat) : (term98 _3741 _3740 _3742) = (term71 _3741 _3740 _3742).
Proof. exact (eq_refl (term98 _3741 _3740 _3742)). Qed.
Lemma lem183661 (_3741 : nat) (_3740 : nat) (_3742 : nat) (h1 : term65) : term71 _3741 _3740 _3742.
Proof. exact (EQ_MP (@lem183660 _3741 _3740 _3742) (@lem183659 _3741 _3740 _3742 h1)). Qed.
Lemma lem183662 (_3743 : nat) (h1 : term31) : term99 _3743.
Proof. exact (@lem183652 h1 _3743). Qed.
Lemma lem183663 (_3743 : nat) : (term99 _3743) = (term93 _3743).
Proof. exact (eq_refl (term99 _3743)). Qed.
Lemma lem183664 (_3743 : nat) (h1 : term31) : term93 _3743.
Proof. exact (EQ_MP (@lem183663 _3743) (@lem183662 _3743 h1)). Qed.
Lemma lem183665 (_3743 : nat) (_3744 : nat) (h1 : term31) : term100 _3743 _3744.
Proof. exact (@lem183664 _3743 h1 _3744). Qed.
Lemma lem183666 (_3743 : nat) (_3744 : nat) : (term100 _3743 _3744) = (term89 _3743 _3744).
Proof. exact (eq_refl (term100 _3743 _3744)). Qed.
Lemma lem183667 (_3743 : nat) (_3744 : nat) (h1 : term31) : term89 _3743 _3744.
Proof. exact (EQ_MP (@lem183666 _3743 _3744) (@lem183665 _3743 _3744 h1)). Qed.
Lemma lem183671 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183673 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183675 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term24 m n p.
Proof. exact (h1). Qed.
Lemma lem183686 (_3741 : nat) (_3740 : nat) (_3742 : nat) : (term71 _3741 _3740 _3742) = (term101 _3741 _3740 _3742).
Proof. exact (@lem183020 (term102 _3740 _3741) (term103 _3741 _3742) (Peano.lt _3740 _3742)). Qed.
Lemma lem183687 (_3741 : nat) (_3740 : nat) (_3742 : nat) (h1 : term65) : term101 _3741 _3740 _3742.
Proof. exact (EQ_MP (@lem183686 _3741 _3740 _3742) (@lem183661 _3741 _3740 _3742 h1)). Qed.
Lemma lem183699 (_3743 : nat) (_3744 : nat) (h1 : term31) : term104 _3743 _3744.
Proof. exact (proj2 (@lem183667 _3743 _3744 h1)). Qed.
Lemma lem183809 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (h1). Qed.
Lemma lem183810 (n : nat) (h1 : term19 n) : term105 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem183809 n h1). Qed.
Lemma lem183812 (p : Prop) : (term106 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem183813 (n : nat) : (term105 n) = (term19 n).
Proof. exact (@lem183812 (n = (NUMERAL 0))). Qed.
Lemma lem183814 (n : nat) (h1 : term19 n) : term19 n.
Proof. exact (EQ_MP (@lem183813 n) (@lem183810 n h1)). Qed.
Lemma lem183820 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem183821 (_3743 : nat) (_3744 : nat) : (term104 _3743 _3744) = (term107 _3743 _3744).
Proof. exact (@lem183820 (term91 _3743 _3744) (_3744 = (NUMERAL 0))). Qed.
Lemma lem183829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem183830 (_3743 : nat) (_3744 : nat) : (term108 _3743 _3744) = (term109 _3743 _3744).
Proof. exact (MK_COMB (@lem183829) (@lem183821 _3743 _3744)). Qed.
Lemma lem183838 (_3743 : nat) (_3744 : nat) : (term107 _3743 _3744) = (term107 _3743 _3744).
Proof. exact (eq_refl (term107 _3743 _3744)). Qed.
Lemma lem183839 (_3743 : nat) (_3744 : nat) : ((term104 _3743 _3744) = (term107 _3743 _3744)) = ((term107 _3743 _3744) = (term107 _3743 _3744)).
Proof. exact (MK_COMB (@lem183830 _3743 _3744) (@lem183838 _3743 _3744)). Qed.
Lemma lem183841 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem183842 (x : Prop) : (x = x) = True.
Proof. exact (@lem183841 Prop x). Qed.
Lemma lem183843 (_3743 : nat) (_3744 : nat) : ((term107 _3743 _3744) = (term107 _3743 _3744)) = True.
Proof. exact (@lem183842 (term107 _3743 _3744)). Qed.
Lemma lem183844 (_3743 : nat) (_3744 : nat) : ((term104 _3743 _3744) = (term107 _3743 _3744)) = True.
Proof. exact (TRANS (@lem183839 _3743 _3744) (@lem183843 _3743 _3744)). Qed.
Lemma lem183845 (_3743 : nat) (_3744 : nat) : True = ((term104 _3743 _3744) = (term107 _3743 _3744)).
Proof. exact (SYM (@lem183844 _3743 _3744)). Qed.
Lemma lem183846 (_3743 : nat) (_3744 : nat) : (term104 _3743 _3744) = (term107 _3743 _3744).
Proof. exact (EQ_MP (@lem183845 _3743 _3744) (@lem0)). Qed.
Lemma lem183847 (_3743 : nat) (_3744 : nat) (h1 : term31) : term107 _3743 _3744.
Proof. exact (EQ_MP (@lem183846 _3743 _3744) (@lem183699 _3743 _3744 h1)). Qed.
Lemma lem183849 (b : Prop) (a : Prop) : (a \/ b) = (term110 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem183852 (_3743 : nat) (_3744 : nat) : (term107 _3743 _3744) = (term111 _3743 _3744).
Proof. exact (@lem183849 (_3744 = (NUMERAL 0)) (term91 _3743 _3744)). Qed.
Lemma lem183855 (_3743 : nat) (_3744 : nat) (h1 : term31) : term111 _3743 _3744.
Proof. exact (EQ_MP (@lem183852 _3743 _3744) (@lem183847 _3743 _3744 h1)). Qed.
Lemma lem183856 (_3743 : nat) (n : nat) (h1 : term31) : term111 _3743 n.
Proof. exact (@lem183855 _3743 n h1). Qed.
Lemma lem183859 (_3743 : nat) (n : nat) (h1 : term31) (h2 : term19 n) : term91 _3743 n.
Proof. exact (@lem183856 _3743 n h1 (@lem183814 n h2)). Qed.
Lemma lem183860 (m : nat) (n : nat) (h1 : term31) (h2 : term19 n) : term91 m n.
Proof. exact (@lem183859 m n h1 h2). Qed.
Lemma lem183861 (m : nat) (n : nat) (h1 : term31) (h2 : term19 n) : term112 m n.
Proof. exact (fun h0 : term113 m n => @lem183860 m n h1 h2). Qed.
Lemma lem183863 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem183864 (m : nat) (n : nat) : (term112 m n) = (term91 m n).
Proof. exact (@lem183863 (term91 m n)). Qed.
Lemma lem183865 (m : nat) (n : nat) (h1 : term31) (h2 : term19 n) : term91 m n.
Proof. exact (EQ_MP (@lem183864 m n) (@lem183861 m n h1 h2)). Qed.
Lemma lem183867 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (h1). Qed.
Lemma lem183868 (n : nat) (p : nat) (h1 : Peano.le n p) : term115 n p.
Proof. exact (fun h0 : term103 n p => @lem183867 n p h1). Qed.
Lemma lem183870 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem183871 (n : nat) (p : nat) : (term115 n p) = (Peano.le n p).
Proof. exact (@lem183870 (Peano.le n p)). Qed.
Lemma lem183872 (n : nat) (p : nat) (h1 : Peano.le n p) : Peano.le n p.
Proof. exact (EQ_MP (@lem183871 n p) (@lem183868 n p h1)). Qed.
Lemma lem183888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem183889 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term116 _3741 _3740 _3742) = (term117 _3740 _3741 _3742).
Proof. exact (@lem183888 (Peano.lt _3740 _3742) (term103 _3741 _3742)). Qed.
Lemma lem183895 (_3740 : nat) (_3741 : nat) : (term118 _3740 _3741) = (term118 _3740 _3741).
Proof. exact (eq_refl (term118 _3740 _3741)). Qed.
Lemma lem183896 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term101 _3741 _3740 _3742) = (term119 _3740 _3741 _3742).
Proof. exact (MK_COMB (@lem183895 _3740 _3741) (@lem183889 _3740 _3741 _3742)). Qed.
Lemma lem183900 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem183901 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term119 _3740 _3741 _3742) = (term120 _3740 _3741 _3742).
Proof. exact (@lem183900 (Peano.lt _3740 _3742) (term102 _3740 _3741) (term103 _3741 _3742)). Qed.
Lemma lem183917 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term101 _3741 _3740 _3742) = (term120 _3740 _3741 _3742).
Proof. exact (TRANS (@lem183896 _3740 _3741 _3742) (@lem183901 _3740 _3741 _3742)). Qed.
Lemma lem183918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem183919 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term121 _3741 _3740 _3742) = (term122 _3740 _3741 _3742).
Proof. exact (MK_COMB (@lem183918) (@lem183917 _3740 _3741 _3742)). Qed.
Lemma lem183935 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term120 _3740 _3741 _3742) = (term120 _3740 _3741 _3742).
Proof. exact (eq_refl (term120 _3740 _3741 _3742)). Qed.
Lemma lem183936 (_3740 : nat) (_3741 : nat) (_3742 : nat) : ((term101 _3741 _3740 _3742) = (term120 _3740 _3741 _3742)) = ((term120 _3740 _3741 _3742) = (term120 _3740 _3741 _3742)).
Proof. exact (MK_COMB (@lem183919 _3740 _3741 _3742) (@lem183935 _3740 _3741 _3742)). Qed.
Lemma lem183938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem183939 (x : Prop) : (x = x) = True.
Proof. exact (@lem183938 Prop x). Qed.
Lemma lem183940 (_3740 : nat) (_3741 : nat) (_3742 : nat) : ((term120 _3740 _3741 _3742) = (term120 _3740 _3741 _3742)) = True.
Proof. exact (@lem183939 (term120 _3740 _3741 _3742)). Qed.
Lemma lem183941 (_3740 : nat) (_3741 : nat) (_3742 : nat) : ((term101 _3741 _3740 _3742) = (term120 _3740 _3741 _3742)) = True.
Proof. exact (TRANS (@lem183936 _3740 _3741 _3742) (@lem183940 _3740 _3741 _3742)). Qed.
Lemma lem183942 (_3740 : nat) (_3741 : nat) (_3742 : nat) : True = ((term101 _3741 _3740 _3742) = (term120 _3740 _3741 _3742)).
Proof. exact (SYM (@lem183941 _3740 _3741 _3742)). Qed.
Lemma lem183943 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term101 _3741 _3740 _3742) = (term120 _3740 _3741 _3742).
Proof. exact (EQ_MP (@lem183942 _3740 _3741 _3742) (@lem0)). Qed.
Lemma lem183944 (_3740 : nat) (_3741 : nat) (_3742 : nat) (h1 : term65) : term120 _3740 _3741 _3742.
Proof. exact (EQ_MP (@lem183943 _3740 _3741 _3742) (@lem183687 _3741 _3740 _3742 h1)). Qed.
Lemma lem183946 (b : Prop) (a : Prop) : (a \/ b) = (term110 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem183947 (_3741 : nat) (_3740 : nat) (_3742 : nat) : (term120 _3740 _3741 _3742) = (term123 _3741 _3740 _3742).
Proof. exact (@lem183946 (term67 _3740 _3741 _3742) (Peano.lt _3740 _3742)). Qed.
Lemma lem183949 (a : Prop) (b : Prop) : (term124 a b) = (term125 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem183950 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term126 _3740 _3741 _3742) = (term127 _3740 _3741 _3742).
Proof. exact (@lem183949 (term102 _3740 _3741) (term103 _3741 _3742)). Qed.
Lemma lem183952 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem183953 (_3740 : nat) (_3741 : nat) : (term129 _3740 _3741) = (Peano.lt _3740 _3741).
Proof. exact (@lem183952 (Peano.lt _3740 _3741)). Qed.
Lemma lem183954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem183955 (_3740 : nat) (_3741 : nat) : (term130 _3740 _3741) = (term131 _3740 _3741).
Proof. exact (MK_COMB (@lem183954) (@lem183953 _3740 _3741)). Qed.
Lemma lem183957 (a : Prop) : (term128 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem183958 (_3741 : nat) (_3742 : nat) : (term132 _3741 _3742) = (Peano.le _3741 _3742).
Proof. exact (@lem183957 (Peano.le _3741 _3742)). Qed.
Lemma lem183959 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term127 _3740 _3741 _3742) = (term72 _3740 _3741 _3742).
Proof. exact (MK_COMB (@lem183955 _3740 _3741) (@lem183958 _3741 _3742)). Qed.
Lemma lem183960 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term126 _3740 _3741 _3742) = (term72 _3740 _3741 _3742).
Proof. exact (TRANS (@lem183950 _3740 _3741 _3742) (@lem183959 _3740 _3741 _3742)). Qed.
Lemma lem183961 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem183962 (_3740 : nat) (_3741 : nat) (_3742 : nat) : (term133 _3740 _3741 _3742) = (term134 _3740 _3741 _3742).
Proof. exact (MK_COMB (@lem183961) (@lem183960 _3740 _3741 _3742)). Qed.
Lemma lem183963 (_3740 : nat) (_3742 : nat) : (Peano.lt _3740 _3742) = (Peano.lt _3740 _3742).
Proof. exact (eq_refl (Peano.lt _3740 _3742)). Qed.
Lemma lem183964 (_3741 : nat) (_3740 : nat) (_3742 : nat) : (term123 _3741 _3740 _3742) = (term59 _3741 _3740 _3742).
Proof. exact (MK_COMB (@lem183962 _3740 _3741 _3742) (@lem183963 _3740 _3742)). Qed.
Lemma lem183965 (_3741 : nat) (_3740 : nat) (_3742 : nat) : (term120 _3740 _3741 _3742) = (term59 _3741 _3740 _3742).
Proof. exact (TRANS (@lem183947 _3741 _3740 _3742) (@lem183964 _3741 _3740 _3742)). Qed.
Lemma lem183967 (m : nat) (n : nat) (p : nat) (h1 : term31) (h2 : term19 n) (h3 : Peano.le n p) : term135 m n p.
Proof. exact (conj (@lem183865 m n h1 h2) (@lem183872 n p h3)). Qed.
Lemma lem183969 (_3741 : nat) (_3740 : nat) (_3742 : nat) (h1 : term65) : term59 _3741 _3740 _3742.
Proof. exact (EQ_MP (@lem183965 _3741 _3740 _3742) (@lem183944 _3740 _3741 _3742 h1)). Qed.
Lemma lem183970 (m : nat) (n : nat) (p : nat) (h1 : term65) : term136 m n p.
Proof. exact (@lem183969 n (Nat.modulo m n) p h1). Qed.
Lemma lem183973 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term19 n) (h4 : Peano.le n p) : term22 m n p.
Proof. exact (@lem183970 m n p h1 (@lem183967 m n p h2 h3 h4)). Qed.
Lemma lem183974 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term19 n) (h4 : Peano.le n p) : term137 m n p.
Proof. exact (fun h0 : term24 m n p => @lem183973 m n p h1 h2 h3 h4). Qed.
Lemma lem183976 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem183977 (m : nat) (n : nat) (p : nat) : (term137 m n p) = (term22 m n p).
Proof. exact (@lem183976 (term22 m n p)). Qed.
Lemma lem183978 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term19 n) (h4 : Peano.le n p) : term22 m n p.
Proof. exact (EQ_MP (@lem183977 m n p) (@lem183974 m n p h1 h2 h3 h4)). Qed.
Lemma lem183981 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem183983 (m : nat) (n : nat) (p : nat) : (term24 m n p) = (term138 m n p).
Proof. exact (@lem183981 (term22 m n p)). Qed.
Lemma lem183986 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) : term138 m n p.
Proof. exact (EQ_MP (@lem183983 m n p) (@lem183675 m n p h1)). Qed.
Lemma lem183989 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (@lem183986 m n p h3 (@lem183978 m n p h1 h2 h4 h5)). Qed.
Lemma lem183990 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : term139.
Proof. exact (fun h0 : ~ False => @lem183989 m n p h1 h2 h3 h4 h5). Qed.
Lemma lem183992 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem183993 : term139 = False.
Proof. exact (@lem183992 False). Qed.
Lemma lem183994 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem183993) (@lem183990 m n p h1 h2 h3 h4 h5)). Qed.
Lemma lem183995 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h6 : term24 m n p => @lem183994 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183675 m n p h3)). Qed.
Lemma lem183996 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem183995 m n p h1 h2 h3 h4 h5) (@lem183675 m n p h3)). Qed.
Lemma lem183997 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (Peano.le n p) = False.
Proof. exact (prop_ext (fun h6 : Peano.le n p => @lem183996 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183673 n p h5)). Qed.
Lemma lem183998 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem183997 m n p h1 h2 h3 h4 h5) (@lem183673 n p h5)). Qed.
Lemma lem183999 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term19 n) = False.
Proof. exact (prop_ext (fun h6 : term19 n => @lem183998 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183671 n h4)). Qed.
Lemma lem184000 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem183999 m n p h1 h2 h3 h4 h5) (@lem183671 n h4)). Qed.
Lemma lem184001 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h6 : term24 m n p => @lem184000 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183601 m n p h3)). Qed.
Lemma lem184002 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184001 m n p h1 h2 h3 h4 h5) (@lem183601 m n p h3)). Qed.
Lemma lem184003 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (Peano.le n p) = False.
Proof. exact (prop_ext (fun h6 : Peano.le n p => @lem184002 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183597 n p h5)). Qed.
Lemma lem184004 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184003 m n p h1 h2 h3 h4 h5) (@lem183597 n p h5)). Qed.
Lemma lem184005 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term19 n) = False.
Proof. exact (prop_ext (fun h6 : term19 n => @lem184004 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183593 n h4)). Qed.
Lemma lem184006 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184005 m n p h1 h2 h3 h4 h5) (@lem183593 n h4)). Qed.
Lemma lem184007 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h6 : term24 m n p => @lem184006 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183601 m n p h3)). Qed.
Lemma lem184008 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184007 m n p h1 h2 h3 h4 h5) (@lem183601 m n p h3)). Qed.
Lemma lem184009 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (Peano.le n p) = False.
Proof. exact (prop_ext (fun h6 : Peano.le n p => @lem184008 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183597 n p h5)). Qed.
Lemma lem184010 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184009 m n p h1 h2 h3 h4 h5) (@lem183597 n p h5)). Qed.
Lemma lem184011 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term19 n) = False.
Proof. exact (prop_ext (fun h6 : term19 n => @lem184010 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183593 n h4)). Qed.
Lemma lem184012 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184011 m n p h1 h2 h3 h4 h5) (@lem183593 n h4)). Qed.
Lemma lem184013 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h6 : term24 m n p => @lem184012 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183504 m n p h3)). Qed.
Lemma lem184014 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184013 m n p h1 h2 h3 h4 h5) (@lem183504 m n p h3)). Qed.
Lemma lem184015 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (Peano.le n p) = False.
Proof. exact (prop_ext (fun h6 : Peano.le n p => @lem184014 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183492 n p h5)). Qed.
Lemma lem184016 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184015 m n p h1 h2 h3 h4 h5) (@lem183492 n p h5)). Qed.
Lemma lem184017 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term19 n) = False.
Proof. exact (prop_ext (fun h6 : term19 n => @lem184016 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183486 n h4)). Qed.
Lemma lem184018 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184017 m n p h1 h2 h3 h4 h5) (@lem183486 n h4)). Qed.
Lemma lem184019 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h6 : term24 m n p => @lem184018 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183317 m n p h3)). Qed.
Lemma lem184020 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184019 m n p h1 h2 h3 h4 h5) (@lem183317 m n p h3)). Qed.
Lemma lem184021 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (Peano.le n p) = False.
Proof. exact (prop_ext (fun h6 : Peano.le n p => @lem184020 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183311 n p h5)). Qed.
Lemma lem184022 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184021 m n p h1 h2 h3 h4 h5) (@lem183311 n p h5)). Qed.
Lemma lem184023 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : (term19 n) = False.
Proof. exact (prop_ext (fun h6 : term19 n => @lem184022 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem183305 n h4)). Qed.
Lemma lem184024 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term31) (h3 : term24 m n p) (h4 : term19 n) (h5 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184023 m n p h1 h2 h3 h4 h5) (@lem183305 n h4)). Qed.
Lemma lem184025 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term24 m n p) (h3 : term19 n) (h4 : Peano.le n p) : term29.
Proof. exact (fun h0 : term31 => @lem184024 m n p h1 h0 h2 h3 h4). Qed.
Lemma lem184026 : term29 = term30.
Proof. exact (@lem69 term31). Qed.
Lemma lem184027 (m : nat) (n : nat) (p : nat) (h1 : term65) (h2 : term24 m n p) (h3 : term19 n) (h4 : Peano.le n p) : term30.
Proof. exact (EQ_MP (@lem184026) (@lem184025 m n p h1 h2 h3 h4)). Qed.
Lemma lem184028 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : term34.
Proof. exact (fun h0 : term65 => @lem184027 m n p h0 h1 h2 h3). Qed.
Lemma lem184029 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : term37 m n p.
Proof. exact (fun h0 : term24 m n p => @lem184028 m n p h0 h1 h2). Qed.
Lemma lem184030 (m : nat) (p : nat) (n : nat) (h1 : term19 n) : term40 m n p.
Proof. exact (fun h0 : Peano.le n p => @lem184029 m n p h1 h0). Qed.
Lemma lem184031 (m : nat) (n : nat) (p : nat) : term42 m n p.
Proof. exact (fun h0 : term19 n => @lem184030 m p n h0). Qed.
Lemma lem184036 (n : nat) (p : nat) : term46 n p.
Proof. exact (fun m : nat => @lem184031 m n p). Qed.
Lemma lem184041 (p : nat) : term50 p.
Proof. exact (fun n : nat => @lem184036 n p). Qed.
Lemma lem184046 : term54.
Proof. exact (fun p : nat => @lem184041 p). Qed.
Lemma lem184047 : term53.
Proof. exact (EQ_MP (@lem183294) (@lem184046)). Qed.
Lemma lem184048 (p : nat) : term140 p.
Proof. exact (@lem184047 p). Qed.
Lemma lem184049 (p : nat) : (term140 p) = (term49 p).
Proof. exact (eq_refl (term140 p)). Qed.
Lemma lem184050 (p : nat) : term49 p.
Proof. exact (EQ_MP (@lem184049 p) (@lem184048 p)). Qed.
Lemma lem184051 (p : nat) (n : nat) : term141 p n.
Proof. exact (@lem184050 p n). Qed.
Lemma lem184052 (n : nat) (p : nat) : (term141 p n) = (term45 n p).
Proof. exact (eq_refl (term141 p n)). Qed.
Lemma lem184053 (n : nat) (p : nat) : term45 n p.
Proof. exact (EQ_MP (@lem184052 n p) (@lem184051 p n)). Qed.
Lemma lem184054 (n : nat) (p : nat) (m : nat) : term142 n p m.
Proof. exact (@lem184053 n p m). Qed.
Lemma lem184055 (m : nat) (n : nat) (p : nat) : (term142 n p m) = (term25 m n p).
Proof. exact (eq_refl (term142 n p m)). Qed.
Lemma lem184056 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (EQ_MP (@lem184055 m n p) (@lem184054 n p m)). Qed.
Lemma lem184058 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem183069 m n p (@lem184056 m n p)). Qed.
Lemma lem184059 (m : nat) (p : nat) (n : nat) (h1 : term19 n) : term39 m n p.
Proof. exact (@lem184058 m n p (@lem183046 n h1)). Qed.
Lemma lem184060 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : term36 m n p.
Proof. exact (@lem184059 m p n h1 (@lem183045 n p h2)). Qed.
Lemma lem184061 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : term33.
Proof. exact (@lem184060 m n p h2 h3 (@lem183054 m n p h1)). Qed.
Lemma lem184062 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : term29.
Proof. exact (@lem184061 m n p h1 h2 h3 (@lem95941)). Qed.
Lemma lem184063 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : False.
Proof. exact (@lem184062 m n p h1 h2 h3 (@lem157261)). Qed.
Lemma lem184064 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : (term24 m n p) = False.
Proof. exact (prop_ext (fun h4 : term24 m n p => @lem184063 m n p h1 h2 h3) (fun h4 : False => @lem183054 m n p h1)). Qed.
Lemma lem184065 (m : nat) (n : nat) (p : nat) (h1 : term24 m n p) (h2 : term19 n) (h3 : Peano.le n p) : False.
Proof. exact (EQ_MP (@lem184064 m n p h1 h2 h3) (@lem183054 m n p h1)). Qed.
Lemma lem184066 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : term23 m n p.
Proof. exact (fun h0 : term24 m n p => @lem184065 m n p h0 h1 h2). Qed.
Lemma lem184067 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : term22 m n p.
Proof. exact (EQ_MP (@lem183053 m n p) (@lem184066 m n p h1 h2)). Qed.
Lemma lem184068 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : (term143 m n p) = (Nat.modulo m n).
Proof. exact (@lem183049 p m n (@lem184067 m n p h1 h2)). Qed.
Lemma lem184069 (n : nat) (p : nat) (h1 : term18 n p) : Peano.le n p.
Proof. exact (proj2 (@lem183044 n p h1)). Qed.
Lemma lem184070 (n : nat) (p : nat) (h1 : term18 n p) : term19 n.
Proof. exact (proj1 (@lem183044 n p h1)). Qed.
Lemma lem184071 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : (Peano.le n p) = ((term143 m n p) = (Nat.modulo m n)).
Proof. exact (prop_ext (fun h3 : Peano.le n p => @lem184068 m n p h1 h2) (fun h3 : (term143 m n p) = (Nat.modulo m n) => @lem183045 n p h2)). Qed.
Lemma lem184072 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : (term143 m n p) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem184071 m n p h1 h2) (@lem183045 n p h2)). Qed.
Lemma lem184073 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : (term19 n) = ((term143 m n p) = (Nat.modulo m n)).
Proof. exact (prop_ext (fun h3 : term19 n => @lem184072 m n p h1 h2) (fun h3 : (term143 m n p) = (Nat.modulo m n) => @lem183046 n h1)). Qed.
Lemma lem184074 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : Peano.le n p) : (term143 m n p) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem184073 m n p h1 h2) (@lem183046 n h1)). Qed.
Lemma lem184075 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : term18 n p) : (Peano.le n p) = ((term143 m n p) = (Nat.modulo m n)).
Proof. exact (prop_ext (fun h3 : Peano.le n p => @lem184074 m n p h1 h3) (fun h3 : (term143 m n p) = (Nat.modulo m n) => @lem184069 n p h2)). Qed.
Lemma lem184076 (m : nat) (n : nat) (p : nat) (h1 : term19 n) (h2 : term18 n p) : (term143 m n p) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem184075 m n p h1 h2) (@lem184069 n p h2)). Qed.
Lemma lem184077 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : (term19 n) = ((term143 m n p) = (Nat.modulo m n)).
Proof. exact (prop_ext (fun h2 : term19 n => @lem184076 m n p h2 h1) (fun h2 : (term143 m n p) = (Nat.modulo m n) => @lem184070 n p h1)). Qed.
Lemma lem184078 (m : nat) (n : nat) (p : nat) (h1 : term18 n p) : (term143 m n p) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem184077 m n p h1) (@lem184070 n p h1)). Qed.
Lemma lem184079 (p : nat) (m : nat) (n : nat) : term144 p m n.
Proof. exact (fun h0 : term18 n p => @lem184078 m n p h0). Qed.
Lemma lem184084 (m : nat) (n : nat) : term145 m n.
Proof. exact (fun p : nat => @lem184079 p m n). Qed.
Lemma lem184089 (m : nat) : term146 m.
Proof. exact (fun n : nat => @lem184084 m n). Qed.
Lemma lem184094 : term147.
Proof. exact (fun m : nat => @lem184089 m). Qed.
