Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_COMPLETE_term_abbrevs.
Require Import ADD1_spec.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import ADD_SYM_spec.
Require Import BOUNDS_IGNORE_spec.
Require Import FORALL_AND_THM_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_SUC_LT_spec.
Require Import LE_TRANS_spec.
Require Import LT_REFL_spec.
Require Import MULT_2_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SUC_spec.
Require Import MULT_SYM_spec.
Require Import NADD_ADD_spec.
Require Import NADD_ARCH_spec.
Require Import NADD_ARCH_LEMMA_spec.
Require Import NADD_EQ_IMP_LE_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_LE_0_spec.
Require Import NADD_LE_LMUL_spec.
Require Import NADD_LE_RADD_spec.
Require Import NADD_LE_TOTAL_spec.
Require Import NADD_LE_TRANS_spec.
Require Import NADD_MUL_spec.
Require Import NADD_MUL_ASSOC_spec.
Require Import NADD_MUL_SYM_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import NADD_OF_NUM_spec.
Require Import NADD_OF_NUM_LE_spec.
Require Import NADD_OF_NUM_MUL_spec.
Require Import NOT_DEF_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import SKOLEM_THM_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import is_nadd_spec.
Require Import nadd_le_spec.
Require Import num_MAX_spec.
Require Import thm0_spec.
Require Import thm1247096_spec.
Require Import thm1262760_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm98_spec.
Lemma lem1296089 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296090 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1296089 h1 x). Qed.
Lemma lem1296091 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1296092 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1296091 x) (@lem1296090 x h1)). Qed.
Lemma lem1296093 (x : nadd) (y : nadd) (h1 : term0) : term3 x y.
Proof. exact (@lem1296092 x h1 y). Qed.
Lemma lem1296094 (y : nadd) (x : nadd) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1296095 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1296094 y x) (@lem1296093 x y h1)). Qed.
Lemma lem1296096 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term5 y x z.
Proof. exact (@lem1296095 y x h1 z). Qed.
Lemma lem1296097 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296098 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1296097 y x z) (@lem1296096 y x z h1)). Qed.
Lemma lem1296099 (y : nadd) (z : nadd) (h1 : nadd_le y z) : nadd_le y z.
Proof. exact (h1). Qed.
Lemma lem1296100 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296098 y x z h1 (@lem1296099 y z h2)). Qed.
Lemma lem1296101 (x : nadd) (y : nadd) (z : nadd) (h1 : nadd_le y z) : term8 y x z.
Proof. exact (fun h0 : term0 => @lem1296100 x y z h0 h1). Qed.
Lemma lem1296102 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296103 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296101 x y z h2 (@lem1296102 h1)). Qed.
Lemma lem1296104 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : nadd_le y z => @lem1296103 x y z h1 h0). Qed.
Lemma lem1296105 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (fun z : nadd => @lem1296104 y x z h1). Qed.
Lemma lem1296106 (y : nadd) (h1 : term0) : term9 y.
Proof. exact (fun x : nadd => @lem1296105 y x h1). Qed.
Lemma lem1296107 (h1 : term0) : term10.
Proof. exact (fun y : nadd => @lem1296106 y h1). Qed.
Lemma lem1296108 : term11.
Proof. exact (fun h0 : term0 => @lem1296107 h0). Qed.
Lemma lem1296109 : term10.
Proof. exact (@lem1296108 (@lem1280016)). Qed.
Lemma lem1296110 (y : nadd) : term12 y.
Proof. exact (@lem1296109 y). Qed.
Lemma lem1296111 (y : nadd) : (term12 y) = (term9 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem1296112 (y : nadd) : term9 y.
Proof. exact (EQ_MP (@lem1296111 y) (@lem1296110 y)). Qed.
Lemma lem1296113 (y : nadd) (x : nadd) : term13 y x.
Proof. exact (@lem1296112 y x). Qed.
Lemma lem1296114 (y : nadd) (x : nadd) : (term13 y x) = (term4 y x).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1296115 (y : nadd) (x : nadd) : term4 y x.
Proof. exact (EQ_MP (@lem1296114 y x) (@lem1296113 y x)). Qed.
Lemma lem1296116 (y : nadd) (x : nadd) (z : nadd) : term5 y x z.
Proof. exact (@lem1296115 y x z). Qed.
Lemma lem1296117 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296119 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296120 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296119 h1 x). Qed.
Lemma lem1296121 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296122 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296121 x) (@lem1296120 x h1)). Qed.
Lemma lem1296123 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296122 x h1 y). Qed.
Lemma lem1296124 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296125 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296124 y x) (@lem1296123 x y h1)). Qed.
Lemma lem1296126 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296125 y x h1 z). Qed.
Lemma lem1296127 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296128 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296127 y x z) (@lem1296126 y x z h1)). Qed.
Lemma lem1296129 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296130 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296128 y x z h1 (@lem1296129 x y z h2)). Qed.
Lemma lem1296131 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296130 x y z h0 h1). Qed.
Lemma lem1296132 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296133 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296132 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296131 x y z h0)). Qed.
Lemma lem1296134 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296135 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296133 x z h2 (@lem1296134 h1)). Qed.
Lemma lem1296136 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296135 x z h1 h0). Qed.
Lemma lem1296137 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296136 x z h1). Qed.
Lemma lem1296138 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296137 x h1). Qed.
Lemma lem1296139 : term28.
Proof. exact (fun h0 : term14 => @lem1296138 h0). Qed.
Lemma lem1296140 : term27.
Proof. exact (@lem1296139 (@lem1270880)). Qed.
Lemma lem1296141 (x : nadd) : term29 x.
Proof. exact (@lem1296140 x). Qed.
Lemma lem1296142 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296143 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296142 x) (@lem1296141 x)). Qed.
Lemma lem1296144 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296143 x z). Qed.
Lemma lem1296145 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296147 (x : nadd) : term31 x.
Proof. exact (@lem1281482 x). Qed.
Lemma lem1296148 (x : nadd) : (term31 x) = (term32 x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1296149 (x : nadd) : term32 x.
Proof. exact (EQ_MP (@lem1296148 x) (@lem1296147 x)). Qed.
Lemma lem1296150 (x : nadd) (y : nadd) : term33 x y.
Proof. exact (@lem1296149 x y). Qed.
Lemma lem1296151 (x : nadd) (y : nadd) : (term33 x y) = (term34 x y).
Proof. exact (eq_refl (term33 x y)). Qed.
Lemma lem1296152 (x : nadd) (y : nadd) : term34 x y.
Proof. exact (EQ_MP (@lem1296151 x y) (@lem1296150 x y)). Qed.
Lemma lem1296153 (x : nadd) (y : nadd) (z : nadd) : term35 x y z.
Proof. exact (@lem1296152 x y z). Qed.
Lemma lem1296154 (z : nadd) (x : nadd) (y : nadd) : (term35 x y z) = ((term36 x y z) = (nadd_le x y)).
Proof. exact (eq_refl (term35 x y z)). Qed.
Lemma lem1296156 (m : nat) : term37 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1296157 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1296158 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1296157 m) (@lem1296156 m)). Qed.
Lemma lem1296159 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1296158 m n). Qed.
Lemma lem1296160 (n : nat) (m : nat) : (term39 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1296162 : term40.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1296163 : term41.
Proof. exact (proj2 (@lem1296162)). Qed.
Lemma lem1296184 : term42.
Proof. exact (proj1 (@lem1296163)). Qed.
Lemma lem1296185 (n : nat) : term43 n.
Proof. exact (@lem1296184 n). Qed.
Lemma lem1296186 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem1296196 : term45.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1296212 : term46.
Proof. exact (proj1 (@lem1296196)). Qed.
Lemma lem1296213 (m : nat) : term47 m.
Proof. exact (@lem1296212 m). Qed.
Lemma lem1296214 (m : nat) : (term47 m) = ((term48 m) = m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1296220 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296221 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296220 h1 x). Qed.
Lemma lem1296222 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296223 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296222 x) (@lem1296221 x h1)). Qed.
Lemma lem1296224 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296223 x h1 y). Qed.
Lemma lem1296225 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296226 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296225 y x) (@lem1296224 x y h1)). Qed.
Lemma lem1296227 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296226 y x h1 z). Qed.
Lemma lem1296228 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296229 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296228 y x z) (@lem1296227 y x z h1)). Qed.
Lemma lem1296230 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296231 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296229 y x z h1 (@lem1296230 x y z h2)). Qed.
Lemma lem1296232 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296231 x y z h0 h1). Qed.
Lemma lem1296233 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296234 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296233 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296232 x y z h0)). Qed.
Lemma lem1296235 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296236 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296234 x z h2 (@lem1296235 h1)). Qed.
Lemma lem1296237 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296236 x z h1 h0). Qed.
Lemma lem1296238 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296237 x z h1). Qed.
Lemma lem1296239 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296238 x h1). Qed.
Lemma lem1296240 : term28.
Proof. exact (fun h0 : term14 => @lem1296239 h0). Qed.
Lemma lem1296241 : term27.
Proof. exact (@lem1296240 (@lem1270880)). Qed.
Lemma lem1296242 (x : nadd) : term29 x.
Proof. exact (@lem1296241 x). Qed.
Lemma lem1296243 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296244 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296243 x) (@lem1296242 x)). Qed.
Lemma lem1296245 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296244 x z). Qed.
Lemma lem1296246 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296248 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1296249 (x : nadd) (h1 : term49) : term50 x.
Proof. exact (@lem1296248 h1 x). Qed.
Lemma lem1296250 (x : nadd) : (term50 x) = (term51 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1296251 (x : nadd) (h1 : term49) : term51 x.
Proof. exact (EQ_MP (@lem1296250 x) (@lem1296249 x h1)). Qed.
Lemma lem1296252 (x : nadd) (y : nadd) (h1 : term49) : term52 x y.
Proof. exact (@lem1296251 x h1 y). Qed.
Lemma lem1296253 (x : nadd) (y : nadd) : (term52 x y) = (term53 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1296254 (x : nadd) (y : nadd) (h1 : term49) : term53 x y.
Proof. exact (EQ_MP (@lem1296253 x y) (@lem1296252 x y h1)). Qed.
Lemma lem1296255 (x : nadd) (y : nadd) (z : nadd) (h1 : term49) : term54 x y z.
Proof. exact (@lem1296254 x y h1 z). Qed.
Lemma lem1296256 (z : nadd) (x : nadd) (y : nadd) : (term54 x y z) = (term55 z x y).
Proof. exact (eq_refl (term54 x y z)). Qed.
Lemma lem1296257 (z : nadd) (x : nadd) (y : nadd) (h1 : term49) : term55 z x y.
Proof. exact (EQ_MP (@lem1296256 z x y) (@lem1296255 x y z h1)). Qed.
Lemma lem1296258 (x : nadd) (y : nadd) (z : nadd) (h1 : term56 x y z) : term56 x y z.
Proof. exact (h1). Qed.
Lemma lem1296259 (x : nadd) (y : nadd) (z : nadd) (h1 : term49) (h2 : term56 x y z) : nadd_le x y.
Proof. exact (@lem1296257 z x y h1 (@lem1296258 x y z h2)). Qed.
Lemma lem1296260 (x : nadd) (y : nadd) (z : nadd) (h1 : term56 x y z) : term57 x y.
Proof. exact (fun h0 : term49 => @lem1296259 x y z h0 h1). Qed.
Lemma lem1296261 (x : nadd) (y : nadd) (h1 : term58 x y) : term58 x y.
Proof. exact (h1). Qed.
Lemma lem1296262 (x : nadd) (y : nadd) (h1 : term58 x y) : term57 x y.
Proof. exact (ex_elim (@lem1296261 x y h1) (fun z : nadd => fun h0 : term59 x y z => @lem1296260 x y z h0)). Qed.
Lemma lem1296263 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1296264 (x : nadd) (y : nadd) (h1 : term49) (h2 : term58 x y) : nadd_le x y.
Proof. exact (@lem1296262 x y h2 (@lem1296263 h1)). Qed.
Lemma lem1296265 (x : nadd) (y : nadd) (h1 : term49) : term60 x y.
Proof. exact (fun h0 : term58 x y => @lem1296264 x y h1 h0). Qed.
Lemma lem1296266 (x : nadd) (h1 : term49) : term61 x.
Proof. exact (fun y : nadd => @lem1296265 x y h1). Qed.
Lemma lem1296267 (h1 : term49) : term62.
Proof. exact (fun x : nadd => @lem1296266 x h1). Qed.
Lemma lem1296268 : term63.
Proof. exact (fun h0 : term49 => @lem1296267 h0). Qed.
Lemma lem1296269 : term62.
Proof. exact (@lem1296268 (@lem1296088)). Qed.
Lemma lem1296270 (x : nadd) : term64 x.
Proof. exact (@lem1296269 x). Qed.
Lemma lem1296271 (x : nadd) : (term64 x) = (term61 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1296272 (x : nadd) : term61 x.
Proof. exact (EQ_MP (@lem1296271 x) (@lem1296270 x)). Qed.
Lemma lem1296273 (x : nadd) (y : nadd) : term65 x y.
Proof. exact (@lem1296272 x y). Qed.
Lemma lem1296274 (x : nadd) (y : nadd) : (term65 x y) = (term60 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1296276 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem1296277 (m : nat) (h1 : term66) : term67 m.
Proof. exact (@lem1296276 h1 m). Qed.
Lemma lem1296278 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem1296279 (m : nat) (h1 : term66) : term68 m.
Proof. exact (EQ_MP (@lem1296278 m) (@lem1296277 m h1)). Qed.
Lemma lem1296280 (m : nat) (n : nat) (h1 : term66) : term69 m n.
Proof. exact (@lem1296279 m h1 n). Qed.
Lemma lem1296281 (n : nat) (m : nat) : (term69 m n) = (term70 n m).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem1296282 (n : nat) (m : nat) (h1 : term66) : term70 n m.
Proof. exact (EQ_MP (@lem1296281 n m) (@lem1296280 m n h1)). Qed.
Lemma lem1296283 (n : nat) (m : nat) (p : nat) (h1 : term66) : term71 n m p.
Proof. exact (@lem1296282 n m h1 p). Qed.
Lemma lem1296284 (n : nat) (m : nat) (p : nat) : (term71 n m p) = (term72 n m p).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem1296285 (n : nat) (m : nat) (p : nat) (h1 : term66) : term72 n m p.
Proof. exact (EQ_MP (@lem1296284 n m p) (@lem1296283 n m p h1)). Qed.
Lemma lem1296286 (m : nat) (n : nat) (p : nat) (h1 : term73 m n p) : term73 m n p.
Proof. exact (h1). Qed.
Lemma lem1296287 (m : nat) (n : nat) (p : nat) (h1 : term66) (h2 : term73 m n p) : Peano.le m p.
Proof. exact (@lem1296285 n m p h1 (@lem1296286 m n p h2)). Qed.
Lemma lem1296288 (m : nat) (n : nat) (p : nat) (h1 : term73 m n p) : term74 m p.
Proof. exact (fun h0 : term66 => @lem1296287 m n p h0 h1). Qed.
Lemma lem1296289 (m : nat) (p : nat) (h1 : term75 m p) : term75 m p.
Proof. exact (h1). Qed.
Lemma lem1296290 (m : nat) (p : nat) (h1 : term75 m p) : term74 m p.
Proof. exact (ex_elim (@lem1296289 m p h1) (fun n : nat => fun h0 : term76 m p n => @lem1296288 m n p h0)). Qed.
Lemma lem1296291 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem1296292 (m : nat) (p : nat) (h1 : term66) (h2 : term75 m p) : Peano.le m p.
Proof. exact (@lem1296290 m p h2 (@lem1296291 h1)). Qed.
Lemma lem1296293 (m : nat) (p : nat) (h1 : term66) : term77 m p.
Proof. exact (fun h0 : term75 m p => @lem1296292 m p h1 h0). Qed.
Lemma lem1296294 (m : nat) (h1 : term66) : term78 m.
Proof. exact (fun p : nat => @lem1296293 m p h1). Qed.
Lemma lem1296295 (h1 : term66) : term79.
Proof. exact (fun m : nat => @lem1296294 m h1). Qed.
Lemma lem1296296 : term80.
Proof. exact (fun h0 : term66 => @lem1296295 h0). Qed.
Lemma lem1296297 : term79.
Proof. exact (@lem1296296 (@lem93743)). Qed.
Lemma lem1296298 (m : nat) : term81 m.
Proof. exact (@lem1296297 m). Qed.
Lemma lem1296299 (m : nat) : (term81 m) = (term78 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem1296300 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem1296299 m) (@lem1296298 m)). Qed.
Lemma lem1296301 (m : nat) (p : nat) : term82 m p.
Proof. exact (@lem1296300 m p). Qed.
Lemma lem1296302 (m : nat) (p : nat) : (term82 m p) = (term77 m p).
Proof. exact (eq_refl (term82 m p)). Qed.
Lemma lem1296304 (m : nat) : term37 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1296305 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1296306 (m : nat) : term38 m.
Proof. exact (EQ_MP (@lem1296305 m) (@lem1296304 m)). Qed.
Lemma lem1296307 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem1296306 m n). Qed.
Lemma lem1296308 (n : nat) (m : nat) : (term39 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem1296310 (P : nat -> nat) : term83 P.
Proof. exact (@lem1262185 P). Qed.
Lemma lem1296311 (P : nat -> nat) : (term83 P) = (term84 P).
Proof. exact (eq_refl (term83 P)). Qed.
Lemma lem1296312 (P : nat -> nat) : term84 P.
Proof. exact (EQ_MP (@lem1296311 P) (@lem1296310 P)). Qed.
Lemma lem1296313 (P : nat -> nat) (Q : nat -> nat) : term85 P Q.
Proof. exact (@lem1296312 P Q). Qed.
Lemma lem1296314 (P : nat -> nat) (Q : nat -> nat) : (term85 P Q) = ((term86 P Q) = (term87 P Q)).
Proof. exact (eq_refl (term85 P Q)). Qed.
Lemma lem1296316 (m : nat) : term88 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1296317 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1296318 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem1296317 m) (@lem1296316 m)). Qed.
Lemma lem1296319 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1296318 m n). Qed.
Lemma lem1296320 (n : nat) (m : nat) : (term90 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1296325 (m : nat) (n : nat) (p : nat) (h1 : (term91 m n p) = (term92 m n p)) : (term91 m n p) = (term92 m n p).
Proof. exact (h1). Qed.
Lemma lem1296326 (m : nat) (n : nat) (p : nat) (h1 : (term91 m n p) = (term92 m n p)) : (term92 m n p) = (term91 m n p).
Proof. exact (SYM (@lem1296325 m n p h1)). Qed.
Lemma lem1296327 (m : nat) (n : nat) (p : nat) (h1 : (term92 m n p) = (term91 m n p)) : (term92 m n p) = (term91 m n p).
Proof. exact (h1). Qed.
Lemma lem1296328 (m : nat) (n : nat) (p : nat) (h1 : (term92 m n p) = (term91 m n p)) : (term91 m n p) = (term92 m n p).
Proof. exact (SYM (@lem1296327 m n p h1)). Qed.
Lemma lem1296329 (m : nat) (n : nat) (p : nat) : ((term91 m n p) = (term92 m n p)) = ((term92 m n p) = (term91 m n p)).
Proof. exact (prop_ext (fun h1 : (term91 m n p) = (term92 m n p) => @lem1296326 m n p h1) (fun h1 : (term92 m n p) = (term91 m n p) => @lem1296328 m n p h1)). Qed.
Lemma lem1296330 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (fun_ext (fun p : nat => @lem1296329 m n p)). Qed.
Lemma lem1296331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1296332 (m : nat) (n : nat) : (term95 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem1296331) (@lem1296330 m n)). Qed.
Lemma lem1296333 (m : nat) : (term97 m) = (term98 m).
Proof. exact (fun_ext (fun n : nat => @lem1296332 m n)). Qed.
Lemma lem1296334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1296335 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem1296334) (@lem1296333 m)). Qed.
Lemma lem1296336 : term101 = term102.
Proof. exact (fun_ext (fun m : nat => @lem1296335 m)). Qed.
Lemma lem1296337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1296338 : term103 = term104.
Proof. exact (MK_COMB (@lem1296337) (@lem1296336)). Qed.
Lemma lem1296339 : term104.
Proof. exact (EQ_MP (@lem1296338) (@lem77960)). Qed.
Lemma lem1296340 (m : nat) : term105 m.
Proof. exact (@lem1296339 m). Qed.
Lemma lem1296341 (m : nat) : (term105 m) = (term100 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem1296342 (m : nat) : term100 m.
Proof. exact (EQ_MP (@lem1296341 m) (@lem1296340 m)). Qed.
Lemma lem1296343 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem1296342 m n). Qed.
Lemma lem1296344 (m : nat) (n : nat) : (term106 m n) = (term96 m n).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem1296345 (m : nat) (n : nat) : term96 m n.
Proof. exact (EQ_MP (@lem1296344 m n) (@lem1296343 m n)). Qed.
Lemma lem1296346 (m : nat) (n : nat) (p : nat) : term107 m n p.
Proof. exact (@lem1296345 m n p). Qed.
Lemma lem1296347 (m : nat) (n : nat) (p : nat) : (term107 m n p) = ((term92 m n p) = (term91 m n p)).
Proof. exact (eq_refl (term107 m n p)). Qed.
Lemma lem1296349 (m : nat) : term108 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1296350 (m : nat) : (term108 m) = (term109 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem1296351 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem1296350 m) (@lem1296349 m)). Qed.
Lemma lem1296352 (m : nat) (n : nat) : term110 m n.
Proof. exact (@lem1296351 m n). Qed.
Lemma lem1296353 (m : nat) (n : nat) : (term110 m n) = (term111 m n).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem1296354 (m : nat) (n : nat) : term111 m n.
Proof. exact (EQ_MP (@lem1296353 m n) (@lem1296352 m n)). Qed.
Lemma lem1296355 (m : nat) (n : nat) (p : nat) : term112 m n p.
Proof. exact (@lem1296354 m n p). Qed.
Lemma lem1296356 (p : nat) (m : nat) (n : nat) : (term112 m n p) = ((term113 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term112 m n p)). Qed.
Lemma lem1296358 (m : nat) : term114 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1296359 (m : nat) : (term114 m) = (term99 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem1296360 (m : nat) : term99 m.
Proof. exact (EQ_MP (@lem1296359 m) (@lem1296358 m)). Qed.
Lemma lem1296361 (m : nat) (n : nat) : term115 m n.
Proof. exact (@lem1296360 m n). Qed.
Lemma lem1296362 (m : nat) (n : nat) : (term115 m n) = (term95 m n).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem1296363 (m : nat) (n : nat) : term95 m n.
Proof. exact (EQ_MP (@lem1296362 m n) (@lem1296361 m n)). Qed.
Lemma lem1296364 (m : nat) (n : nat) (p : nat) : term116 m n p.
Proof. exact (@lem1296363 m n p). Qed.
Lemma lem1296365 (m : nat) (n : nat) (p : nat) : (term116 m n p) = ((term91 m n p) = (term92 m n p)).
Proof. exact (eq_refl (term116 m n p)). Qed.
Lemma lem1296367 : term40.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1296368 : term41.
Proof. exact (proj2 (@lem1296367)). Qed.
Lemma lem1296389 : term42.
Proof. exact (proj1 (@lem1296368)). Qed.
Lemma lem1296390 (n : nat) : term43 n.
Proof. exact (@lem1296389 n). Qed.
Lemma lem1296391 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem1296401 (n : nat) : term117 n.
Proof. exact (@lem84996 n). Qed.
Lemma lem1296402 (n : nat) : (term117 n) = ((term118 n) = (Nat.add n n)).
Proof. exact (eq_refl (term117 n)). Qed.
Lemma lem1296404 (m : nat) : term119 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1296405 (m : nat) : (term119 m) = (term120 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem1296406 (m : nat) : term120 m.
Proof. exact (EQ_MP (@lem1296405 m) (@lem1296404 m)). Qed.
Lemma lem1296407 (m : nat) (n : nat) : term121 m n.
Proof. exact (@lem1296406 m n). Qed.
Lemma lem1296408 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem1296409 (m : nat) (n : nat) : term122 m n.
Proof. exact (EQ_MP (@lem1296408 m n) (@lem1296407 m n)). Qed.
Lemma lem1296410 (m : nat) (n : nat) (p : nat) : term123 m n p.
Proof. exact (@lem1296409 m n p). Qed.
Lemma lem1296411 (m : nat) (n : nat) (p : nat) : (term123 m n p) = ((term124 m n p) = (term125 m n p)).
Proof. exact (eq_refl (term123 m n p)). Qed.
Lemma lem1296413 (m : nat) : term126 m.
Proof. exact (@lem80621 m). Qed.
Lemma lem1296414 (m : nat) : (term126 m) = ((S m) = (term127 m)).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem1296416 (m : nat) : term88 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1296417 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1296418 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem1296417 m) (@lem1296416 m)). Qed.
Lemma lem1296419 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1296418 m n). Qed.
Lemma lem1296420 (n : nat) (m : nat) : (term90 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1296422 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296423 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296422 h1 x). Qed.
Lemma lem1296424 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296425 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296424 x) (@lem1296423 x h1)). Qed.
Lemma lem1296426 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296425 x h1 y). Qed.
Lemma lem1296427 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296428 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296427 y x) (@lem1296426 x y h1)). Qed.
Lemma lem1296429 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296428 y x h1 z). Qed.
Lemma lem1296430 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296431 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296430 y x z) (@lem1296429 y x z h1)). Qed.
Lemma lem1296432 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296433 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296431 y x z h1 (@lem1296432 x y z h2)). Qed.
Lemma lem1296434 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296433 x y z h0 h1). Qed.
Lemma lem1296435 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296436 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296435 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296434 x y z h0)). Qed.
Lemma lem1296437 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296438 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296436 x z h2 (@lem1296437 h1)). Qed.
Lemma lem1296439 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296438 x z h1 h0). Qed.
Lemma lem1296440 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296439 x z h1). Qed.
Lemma lem1296441 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296440 x h1). Qed.
Lemma lem1296442 : term28.
Proof. exact (fun h0 : term14 => @lem1296441 h0). Qed.
Lemma lem1296443 : term27.
Proof. exact (@lem1296442 (@lem1270880)). Qed.
Lemma lem1296444 (x : nadd) : term29 x.
Proof. exact (@lem1296443 x). Qed.
Lemma lem1296445 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296446 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296445 x) (@lem1296444 x)). Qed.
Lemma lem1296447 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296446 x z). Qed.
Lemma lem1296448 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296450 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1296451 (x : nadd) (h1 : term49) : term50 x.
Proof. exact (@lem1296450 h1 x). Qed.
Lemma lem1296452 (x : nadd) : (term50 x) = (term51 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1296453 (x : nadd) (h1 : term49) : term51 x.
Proof. exact (EQ_MP (@lem1296452 x) (@lem1296451 x h1)). Qed.
Lemma lem1296454 (x : nadd) (y : nadd) (h1 : term49) : term52 x y.
Proof. exact (@lem1296453 x h1 y). Qed.
Lemma lem1296455 (x : nadd) (y : nadd) : (term52 x y) = (term53 x y).
Proof. exact (eq_refl (term52 x y)). Qed.
Lemma lem1296456 (x : nadd) (y : nadd) (h1 : term49) : term53 x y.
Proof. exact (EQ_MP (@lem1296455 x y) (@lem1296454 x y h1)). Qed.
Lemma lem1296457 (x : nadd) (y : nadd) (z : nadd) (h1 : term49) : term54 x y z.
Proof. exact (@lem1296456 x y h1 z). Qed.
Lemma lem1296458 (z : nadd) (x : nadd) (y : nadd) : (term54 x y z) = (term55 z x y).
Proof. exact (eq_refl (term54 x y z)). Qed.
Lemma lem1296459 (z : nadd) (x : nadd) (y : nadd) (h1 : term49) : term55 z x y.
Proof. exact (EQ_MP (@lem1296458 z x y) (@lem1296457 x y z h1)). Qed.
Lemma lem1296460 (x : nadd) (y : nadd) (z : nadd) (h1 : term56 x y z) : term56 x y z.
Proof. exact (h1). Qed.
Lemma lem1296461 (x : nadd) (y : nadd) (z : nadd) (h1 : term49) (h2 : term56 x y z) : nadd_le x y.
Proof. exact (@lem1296459 z x y h1 (@lem1296460 x y z h2)). Qed.
Lemma lem1296462 (x : nadd) (y : nadd) (z : nadd) (h1 : term56 x y z) : term57 x y.
Proof. exact (fun h0 : term49 => @lem1296461 x y z h0 h1). Qed.
Lemma lem1296463 (x : nadd) (y : nadd) (h1 : term58 x y) : term58 x y.
Proof. exact (h1). Qed.
Lemma lem1296464 (x : nadd) (y : nadd) (h1 : term58 x y) : term57 x y.
Proof. exact (ex_elim (@lem1296463 x y h1) (fun z : nadd => fun h0 : term59 x y z => @lem1296462 x y z h0)). Qed.
Lemma lem1296465 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1296466 (x : nadd) (y : nadd) (h1 : term49) (h2 : term58 x y) : nadd_le x y.
Proof. exact (@lem1296464 x y h2 (@lem1296465 h1)). Qed.
Lemma lem1296467 (x : nadd) (y : nadd) (h1 : term49) : term60 x y.
Proof. exact (fun h0 : term58 x y => @lem1296466 x y h1 h0). Qed.
Lemma lem1296468 (x : nadd) (h1 : term49) : term61 x.
Proof. exact (fun y : nadd => @lem1296467 x y h1). Qed.
Lemma lem1296469 (h1 : term49) : term62.
Proof. exact (fun x : nadd => @lem1296468 x h1). Qed.
Lemma lem1296470 : term63.
Proof. exact (fun h0 : term49 => @lem1296469 h0). Qed.
Lemma lem1296471 : term62.
Proof. exact (@lem1296470 (@lem1296088)). Qed.
Lemma lem1296472 (x : nadd) : term64 x.
Proof. exact (@lem1296471 x). Qed.
Lemma lem1296473 (x : nadd) : (term64 x) = (term61 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1296474 (x : nadd) : term61 x.
Proof. exact (EQ_MP (@lem1296473 x) (@lem1296472 x)). Qed.
Lemma lem1296475 (x : nadd) (y : nadd) : term65 x y.
Proof. exact (@lem1296474 x y). Qed.
Lemma lem1296476 (x : nadd) (y : nadd) : (term65 x y) = (term60 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1296478 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem1296479 (m : nat) (h1 : term66) : term67 m.
Proof. exact (@lem1296478 h1 m). Qed.
Lemma lem1296480 (m : nat) : (term67 m) = (term68 m).
Proof. exact (eq_refl (term67 m)). Qed.
Lemma lem1296481 (m : nat) (h1 : term66) : term68 m.
Proof. exact (EQ_MP (@lem1296480 m) (@lem1296479 m h1)). Qed.
Lemma lem1296482 (m : nat) (n : nat) (h1 : term66) : term69 m n.
Proof. exact (@lem1296481 m h1 n). Qed.
Lemma lem1296483 (n : nat) (m : nat) : (term69 m n) = (term70 n m).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem1296484 (n : nat) (m : nat) (h1 : term66) : term70 n m.
Proof. exact (EQ_MP (@lem1296483 n m) (@lem1296482 m n h1)). Qed.
Lemma lem1296485 (n : nat) (m : nat) (p : nat) (h1 : term66) : term71 n m p.
Proof. exact (@lem1296484 n m h1 p). Qed.
Lemma lem1296486 (n : nat) (m : nat) (p : nat) : (term71 n m p) = (term72 n m p).
Proof. exact (eq_refl (term71 n m p)). Qed.
Lemma lem1296487 (n : nat) (m : nat) (p : nat) (h1 : term66) : term72 n m p.
Proof. exact (EQ_MP (@lem1296486 n m p) (@lem1296485 n m p h1)). Qed.
Lemma lem1296488 (m : nat) (n : nat) (p : nat) (h1 : term73 m n p) : term73 m n p.
Proof. exact (h1). Qed.
Lemma lem1296489 (m : nat) (n : nat) (p : nat) (h1 : term66) (h2 : term73 m n p) : Peano.le m p.
Proof. exact (@lem1296487 n m p h1 (@lem1296488 m n p h2)). Qed.
Lemma lem1296490 (m : nat) (n : nat) (p : nat) (h1 : term73 m n p) : term74 m p.
Proof. exact (fun h0 : term66 => @lem1296489 m n p h0 h1). Qed.
Lemma lem1296491 (m : nat) (p : nat) (h1 : term75 m p) : term75 m p.
Proof. exact (h1). Qed.
Lemma lem1296492 (m : nat) (p : nat) (h1 : term75 m p) : term74 m p.
Proof. exact (ex_elim (@lem1296491 m p h1) (fun n : nat => fun h0 : term76 m p n => @lem1296490 m n p h0)). Qed.
Lemma lem1296493 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem1296494 (m : nat) (p : nat) (h1 : term66) (h2 : term75 m p) : Peano.le m p.
Proof. exact (@lem1296492 m p h2 (@lem1296493 h1)). Qed.
Lemma lem1296495 (m : nat) (p : nat) (h1 : term66) : term77 m p.
Proof. exact (fun h0 : term75 m p => @lem1296494 m p h1 h0). Qed.
Lemma lem1296496 (m : nat) (h1 : term66) : term78 m.
Proof. exact (fun p : nat => @lem1296495 m p h1). Qed.
Lemma lem1296497 (h1 : term66) : term79.
Proof. exact (fun m : nat => @lem1296496 m h1). Qed.
Lemma lem1296498 : term80.
Proof. exact (fun h0 : term66 => @lem1296497 h0). Qed.
Lemma lem1296499 : term79.
Proof. exact (@lem1296498 (@lem93743)). Qed.
Lemma lem1296500 (m : nat) : term81 m.
Proof. exact (@lem1296499 m). Qed.
Lemma lem1296501 (m : nat) : (term81 m) = (term78 m).
Proof. exact (eq_refl (term81 m)). Qed.
Lemma lem1296502 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem1296501 m) (@lem1296500 m)). Qed.
Lemma lem1296503 (m : nat) (p : nat) : term82 m p.
Proof. exact (@lem1296502 m p). Qed.
Lemma lem1296504 (m : nat) (p : nat) : (term82 m p) = (term77 m p).
Proof. exact (eq_refl (term82 m p)). Qed.
Lemma lem1296506 (m : nat) : term88 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1296507 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1296508 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem1296507 m) (@lem1296506 m)). Qed.
Lemma lem1296509 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1296508 m n). Qed.
Lemma lem1296510 (n : nat) (m : nat) : (term90 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1296512 {A B : Type'} (P : type1413 A B) : term128 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem1296513 {A B : Type'} (P : type1413 A B) : (term128 A B P) = ((term129 A B P) = (term130 A B P)).
Proof. exact (eq_refl (term128 A B P)). Qed.
Lemma lem1296515 {A : Type'} (P : A -> Prop) : term131 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem1296516 {A : Type'} (P : A -> Prop) : (term131 A P) = (term132 A P).
Proof. exact (eq_refl (term131 A P)). Qed.
Lemma lem1296517 {A : Type'} (P : A -> Prop) : term132 A P.
Proof. exact (EQ_MP (@lem1296516 A P) (@lem1296515 A P)). Qed.
Lemma lem1296518 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term133 A P Q.
Proof. exact (@lem1296517 A P Q). Qed.
Lemma lem1296519 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term133 A P Q) = ((term134 A P Q) = (term135 A P Q)).
Proof. exact (eq_refl (term133 A P Q)). Qed.
Lemma lem1296521 : term40.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1296522 : term41.
Proof. exact (proj2 (@lem1296521)). Qed.
Lemma lem1296543 : term42.
Proof. exact (proj1 (@lem1296522)). Qed.
Lemma lem1296544 (n : nat) : term43 n.
Proof. exact (@lem1296543 n). Qed.
Lemma lem1296545 (n : nat) : (term43 n) = ((term44 n) = n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem1296555 (m : nat) : term136 m.
Proof. exact (@lem1247096 m). Qed.
Lemma lem1296556 (m : nat) : (term136 m) = (term137 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem1296557 (m : nat) : term137 m.
Proof. exact (EQ_MP (@lem1296556 m) (@lem1296555 m)). Qed.
Lemma lem1296558 (m : nat) (n : nat) : term138 m n.
Proof. exact (@lem1296557 m n). Qed.
Lemma lem1296559 (n : nat) (m : nat) : (term138 m n) = (term139 n m).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem1296560 (n : nat) (m : nat) : term139 n m.
Proof. exact (EQ_MP (@lem1296559 n m) (@lem1296558 m n)). Qed.
Lemma lem1296561 (n : nat) (m : nat) (p : nat) : term140 n m p.
Proof. exact (@lem1296560 n m p). Qed.
Lemma lem1296562 (n : nat) (m : nat) (p : nat) : (term140 n m p) = ((term141 m n p) = (term142 n m p)).
Proof. exact (eq_refl (term140 n m p)). Qed.
Lemma lem1296564 (x : nat -> nat) : term143 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1296565 (x : nat -> nat) : (term143 x) = ((is_nadd x) = (term144 x)).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1296567 (r : nat -> nat) (h1 : (is_nadd r) = ((term145 r) = r)) : (is_nadd r) = ((term145 r) = r).
Proof. exact (h1). Qed.
Lemma lem1296568 (r : nat -> nat) (h1 : (is_nadd r) = ((term145 r) = r)) : ((term145 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1296567 r h1)). Qed.
Lemma lem1296569 (r : nat -> nat) (h1 : ((term145 r) = r) = (is_nadd r)) : ((term145 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1296570 (r : nat -> nat) (h1 : ((term145 r) = r) = (is_nadd r)) : (is_nadd r) = ((term145 r) = r).
Proof. exact (SYM (@lem1296569 r h1)). Qed.
Lemma lem1296571 (r : nat -> nat) : ((is_nadd r) = ((term145 r) = r)) = (((term145 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term145 r) = r) => @lem1296568 r h1) (fun h1 : ((term145 r) = r) = (is_nadd r) => @lem1296570 r h1)). Qed.
Lemma lem1296573 (m : nat) : term146 m.
Proof. exact (@lem1279539 m). Qed.
Lemma lem1296574 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem1296575 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem1296574 m) (@lem1296573 m)). Qed.
Lemma lem1296576 (m : nat) (n : nat) : term148 m n.
Proof. exact (@lem1296575 m n). Qed.
Lemma lem1296577 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem1296578 (m : nat) (n : nat) : term149 m n.
Proof. exact (EQ_MP (@lem1296577 m n) (@lem1296576 m n)). Qed.
Lemma lem1296579 (m : nat) (n : nat) : (term149 m n) = ((term149 m n) = True).
Proof. exact (@lem7 (term149 m n)). Qed.
Lemma lem1296581 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296582 (x : nadd) (h1 : term150) : term151 x.
Proof. exact (@lem1296581 h1 x). Qed.
Lemma lem1296583 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296584 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (EQ_MP (@lem1296583 x) (@lem1296582 x h1)). Qed.
Lemma lem1296585 (x : nadd) (y : nadd) (h1 : term150) : term153 x y.
Proof. exact (@lem1296584 x h1 y). Qed.
Lemma lem1296586 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296587 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (EQ_MP (@lem1296586 x y) (@lem1296585 x y h1)). Qed.
Lemma lem1296588 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1296589 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296587 x y h1 (@lem1296588 x y h2)). Qed.
Lemma lem1296590 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term155 x y.
Proof. exact (fun h0 : term150 => @lem1296589 x y h0 h1). Qed.
Lemma lem1296591 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296592 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296590 x y h2 (@lem1296591 h1)). Qed.
Lemma lem1296593 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1296592 x y h1 h0). Qed.
Lemma lem1296594 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (fun y : nadd => @lem1296593 x y h1). Qed.
Lemma lem1296595 (h1 : term150) : term150.
Proof. exact (fun x : nadd => @lem1296594 x h1). Qed.
Lemma lem1296596 : term156.
Proof. exact (fun h0 : term150 => @lem1296595 h0). Qed.
Lemma lem1296597 : term150.
Proof. exact (@lem1296596 (@lem1279763)). Qed.
Lemma lem1296598 (x : nadd) : term151 x.
Proof. exact (@lem1296597 x). Qed.
Lemma lem1296599 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296600 (x : nadd) : term152 x.
Proof. exact (EQ_MP (@lem1296599 x) (@lem1296598 x)). Qed.
Lemma lem1296601 (x : nadd) (y : nadd) : term153 x y.
Proof. exact (@lem1296600 x y). Qed.
Lemma lem1296602 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296606 (m : nat) (n : nat) (h1 : (term157 m n) = (term158 m n)) : (term157 m n) = (term158 m n).
Proof. exact (h1). Qed.
Lemma lem1296607 (m : nat) (n : nat) (h1 : (term157 m n) = (term158 m n)) : (term158 m n) = (term157 m n).
Proof. exact (SYM (@lem1296606 m n h1)). Qed.
Lemma lem1296608 (m : nat) (n : nat) (h1 : (term158 m n) = (term157 m n)) : (term158 m n) = (term157 m n).
Proof. exact (h1). Qed.
Lemma lem1296609 (m : nat) (n : nat) (h1 : (term158 m n) = (term157 m n)) : (term157 m n) = (term158 m n).
Proof. exact (SYM (@lem1296608 m n h1)). Qed.
Lemma lem1296610 (m : nat) (n : nat) : ((term157 m n) = (term158 m n)) = ((term158 m n) = (term157 m n)).
Proof. exact (prop_ext (fun h1 : (term157 m n) = (term158 m n) => @lem1296607 m n h1) (fun h1 : (term158 m n) = (term157 m n) => @lem1296609 m n h1)). Qed.
Lemma lem1296611 (m : nat) : (term159 m) = (term160 m).
Proof. exact (fun_ext (fun n : nat => @lem1296610 m n)). Qed.
Lemma lem1296612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1296613 (m : nat) : (term161 m) = (term162 m).
Proof. exact (MK_COMB (@lem1296612) (@lem1296611 m)). Qed.
Lemma lem1296614 : term163 = term164.
Proof. exact (fun_ext (fun m : nat => @lem1296613 m)). Qed.
Lemma lem1296615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1296616 : term165 = term166.
Proof. exact (MK_COMB (@lem1296615) (@lem1296614)). Qed.
Lemma lem1296617 : term166.
Proof. exact (EQ_MP (@lem1296616) (@lem81331)). Qed.
Lemma lem1296618 (m : nat) : term167 m.
Proof. exact (@lem1296617 m). Qed.
Lemma lem1296619 (m : nat) : (term167 m) = (term162 m).
Proof. exact (eq_refl (term167 m)). Qed.
Lemma lem1296620 (m : nat) : term162 m.
Proof. exact (EQ_MP (@lem1296619 m) (@lem1296618 m)). Qed.
Lemma lem1296621 (m : nat) (n : nat) : term168 m n.
Proof. exact (@lem1296620 m n). Qed.
Lemma lem1296622 (m : nat) (n : nat) : (term168 m n) = ((term158 m n) = (term157 m n)).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem1296624 (m : nat) : term88 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1296625 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1296626 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem1296625 m) (@lem1296624 m)). Qed.
Lemma lem1296627 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem1296626 m n). Qed.
Lemma lem1296628 (n : nat) (m : nat) : (term90 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem1296630 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296631 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1296630 h1 x). Qed.
Lemma lem1296632 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1296633 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1296632 x) (@lem1296631 x h1)). Qed.
Lemma lem1296634 (x : nadd) (y : nadd) (h1 : term0) : term3 x y.
Proof. exact (@lem1296633 x h1 y). Qed.
Lemma lem1296635 (y : nadd) (x : nadd) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1296636 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1296635 y x) (@lem1296634 x y h1)). Qed.
Lemma lem1296637 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term5 y x z.
Proof. exact (@lem1296636 y x h1 z). Qed.
Lemma lem1296638 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296639 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1296638 y x z) (@lem1296637 y x z h1)). Qed.
Lemma lem1296640 (y : nadd) (z : nadd) (h1 : nadd_le y z) : nadd_le y z.
Proof. exact (h1). Qed.
Lemma lem1296641 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296639 y x z h1 (@lem1296640 y z h2)). Qed.
Lemma lem1296642 (x : nadd) (y : nadd) (z : nadd) (h1 : nadd_le y z) : term8 y x z.
Proof. exact (fun h0 : term0 => @lem1296641 x y z h0 h1). Qed.
Lemma lem1296643 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296644 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296642 x y z h2 (@lem1296643 h1)). Qed.
Lemma lem1296645 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : nadd_le y z => @lem1296644 x y z h1 h0). Qed.
Lemma lem1296646 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (fun z : nadd => @lem1296645 y x z h1). Qed.
Lemma lem1296647 (y : nadd) (h1 : term0) : term9 y.
Proof. exact (fun x : nadd => @lem1296646 y x h1). Qed.
Lemma lem1296648 (h1 : term0) : term10.
Proof. exact (fun y : nadd => @lem1296647 y h1). Qed.
Lemma lem1296649 : term11.
Proof. exact (fun h0 : term0 => @lem1296648 h0). Qed.
Lemma lem1296650 : term10.
Proof. exact (@lem1296649 (@lem1280016)). Qed.
Lemma lem1296651 (y : nadd) : term12 y.
Proof. exact (@lem1296650 y). Qed.
Lemma lem1296652 (y : nadd) : (term12 y) = (term9 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem1296653 (y : nadd) : term9 y.
Proof. exact (EQ_MP (@lem1296652 y) (@lem1296651 y)). Qed.
Lemma lem1296654 (y : nadd) (x : nadd) : term13 y x.
Proof. exact (@lem1296653 y x). Qed.
Lemma lem1296655 (y : nadd) (x : nadd) : (term13 y x) = (term4 y x).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1296656 (y : nadd) (x : nadd) : term4 y x.
Proof. exact (EQ_MP (@lem1296655 y x) (@lem1296654 y x)). Qed.
Lemma lem1296657 (y : nadd) (x : nadd) (z : nadd) : term5 y x z.
Proof. exact (@lem1296656 y x z). Qed.
Lemma lem1296658 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296660 (x : nadd) : term169 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1296661 (x : nadd) : (term169 x) = (nadd_eq x x).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem1296662 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1296661 x) (@lem1296660 x)). Qed.
Lemma lem1296663 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1296665 (x : nadd) : term170 x.
Proof. exact (@lem1278399 x). Qed.
Lemma lem1296666 (x : nadd) : (term170 x) = (term171 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1296667 (x : nadd) : term171 x.
Proof. exact (EQ_MP (@lem1296666 x) (@lem1296665 x)). Qed.
Lemma lem1296668 (x : nadd) (y : nadd) : term172 x y.
Proof. exact (@lem1296667 x y). Qed.
Lemma lem1296669 (y : nadd) (x : nadd) : (term172 x y) = (term173 y x).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1296670 (y : nadd) (x : nadd) : term173 y x.
Proof. exact (EQ_MP (@lem1296669 y x) (@lem1296668 x y)). Qed.
Lemma lem1296671 (y : nadd) (x : nadd) : (term173 y x) = ((term173 y x) = True).
Proof. exact (@lem7 (term173 y x)). Qed.
Lemma lem1296673 (h1 : term174) : term174.
Proof. exact (h1). Qed.
Lemma lem1296674 (x : nadd) (h1 : term174) : term175 x.
Proof. exact (@lem1296673 h1 x). Qed.
Lemma lem1296675 (x : nadd) : (term175 x) = (term176 x).
Proof. exact (eq_refl (term175 x)). Qed.
Lemma lem1296676 (x : nadd) (h1 : term174) : term176 x.
Proof. exact (EQ_MP (@lem1296675 x) (@lem1296674 x h1)). Qed.
Lemma lem1296677 (x : nadd) (x' : nadd) (h1 : term174) : term177 x x'.
Proof. exact (@lem1296676 x h1 x'). Qed.
Lemma lem1296678 (x : nadd) (x' : nadd) : (term177 x x') = (term178 x x').
Proof. exact (eq_refl (term177 x x')). Qed.
Lemma lem1296679 (x : nadd) (x' : nadd) (h1 : term174) : term178 x x'.
Proof. exact (EQ_MP (@lem1296678 x x') (@lem1296677 x x' h1)). Qed.
Lemma lem1296680 (x : nadd) (x' : nadd) (y : nadd) (h1 : term174) : term179 x x' y.
Proof. exact (@lem1296679 x x' h1 y). Qed.
Lemma lem1296681 (x : nadd) (y : nadd) (x' : nadd) : (term179 x x' y) = (term180 x y x').
Proof. exact (eq_refl (term179 x x' y)). Qed.
Lemma lem1296682 (x : nadd) (y : nadd) (x' : nadd) (h1 : term174) : term180 x y x'.
Proof. exact (EQ_MP (@lem1296681 x y x') (@lem1296680 x x' y h1)). Qed.
Lemma lem1296683 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term174) : term181 x y x' y'.
Proof. exact (@lem1296682 x y x' h1 y'). Qed.
Lemma lem1296684 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term181 x y x' y') = (term182 x y x' y').
Proof. exact (eq_refl (term181 x y x' y')). Qed.
Lemma lem1296685 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term174) : term182 x y x' y'.
Proof. exact (EQ_MP (@lem1296684 x y x' y') (@lem1296683 x y x' y' h1)). Qed.
Lemma lem1296686 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term183 x x' y y') : term183 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1296687 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term174) (h2 : term183 x x' y y') : term184 x y x' y'.
Proof. exact (@lem1296685 x y x' y' h1 (@lem1296686 x x' y y' h2)). Qed.
Lemma lem1296688 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term183 x x' y y') : term185 x y x' y'.
Proof. exact (fun h0 : term174 => @lem1296687 x x' y y' h0 h1). Qed.
Lemma lem1296689 (h1 : term174) : term174.
Proof. exact (h1). Qed.
Lemma lem1296690 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term174) (h2 : term183 x x' y y') : term184 x y x' y'.
Proof. exact (@lem1296688 x x' y y' h2 (@lem1296689 h1)). Qed.
Lemma lem1296691 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term174) : term182 x y x' y'.
Proof. exact (fun h0 : term183 x x' y y' => @lem1296690 x x' y y' h1 h0). Qed.
Lemma lem1296692 (x : nadd) (y : nadd) (x' : nadd) (h1 : term174) : term180 x y x'.
Proof. exact (fun y' : nadd => @lem1296691 x y x' y' h1). Qed.
Lemma lem1296693 (x : nadd) (y : nadd) (h1 : term174) : term186 x y.
Proof. exact (fun x' : nadd => @lem1296692 x y x' h1). Qed.
Lemma lem1296694 (x : nadd) (h1 : term174) : term187 x.
Proof. exact (fun y : nadd => @lem1296693 x y h1). Qed.
Lemma lem1296695 (h1 : term174) : term188.
Proof. exact (fun x : nadd => @lem1296694 x h1). Qed.
Lemma lem1296696 : term189.
Proof. exact (fun h0 : term174 => @lem1296695 h0). Qed.
Lemma lem1296697 : term188.
Proof. exact (@lem1296696 (@lem1279298)). Qed.
Lemma lem1296698 (x : nadd) : term190 x.
Proof. exact (@lem1296697 x). Qed.
Lemma lem1296699 (x : nadd) : (term190 x) = (term187 x).
Proof. exact (eq_refl (term190 x)). Qed.
Lemma lem1296700 (x : nadd) : term187 x.
Proof. exact (EQ_MP (@lem1296699 x) (@lem1296698 x)). Qed.
Lemma lem1296701 (x : nadd) (y : nadd) : term191 x y.
Proof. exact (@lem1296700 x y). Qed.
Lemma lem1296702 (x : nadd) (y : nadd) : (term191 x y) = (term186 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1296703 (x : nadd) (y : nadd) : term186 x y.
Proof. exact (EQ_MP (@lem1296702 x y) (@lem1296701 x y)). Qed.
Lemma lem1296704 (x : nadd) (y : nadd) (x' : nadd) : term192 x y x'.
Proof. exact (@lem1296703 x y x'). Qed.
Lemma lem1296705 (x : nadd) (y : nadd) (x' : nadd) : (term192 x y x') = (term180 x y x').
Proof. exact (eq_refl (term192 x y x')). Qed.
Lemma lem1296706 (x : nadd) (y : nadd) (x' : nadd) : term180 x y x'.
Proof. exact (EQ_MP (@lem1296705 x y x') (@lem1296704 x y x')). Qed.
Lemma lem1296707 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term181 x y x' y'.
Proof. exact (@lem1296706 x y x' y'). Qed.
Lemma lem1296708 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term181 x y x' y') = (term182 x y x' y').
Proof. exact (eq_refl (term181 x y x' y')). Qed.
Lemma lem1296710 (x : nadd) : term193 x.
Proof. exact (@lem1268060 x). Qed.
Lemma lem1296711 (x : nadd) : (term193 x) = (term194 x).
Proof. exact (eq_refl (term193 x)). Qed.
Lemma lem1296712 (x : nadd) : term194 x.
Proof. exact (EQ_MP (@lem1296711 x) (@lem1296710 x)). Qed.
Lemma lem1296713 (x : nadd) (y : nadd) : term195 x y.
Proof. exact (@lem1296712 x y). Qed.
Lemma lem1296714 (y : nadd) (x : nadd) : (term195 x y) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1296729 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1296714 y x) (@lem1296713 x y)). Qed.
Lemma lem1296730 (x : nadd) (y : nadd) (z : nadd) : (term196 x y z) = (term197 x y z).
Proof. exact (@lem1296729 (term198 x y z) (term199 x y z)). Qed.
Lemma lem1296731 (x : nadd) (y : nadd) : (term200 x y) = (term201 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1296730 x y z)). Qed.
Lemma lem1296732 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1296733 (x : nadd) (y : nadd) : (term202 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1296732) (@lem1296731 x y)). Qed.
Lemma lem1296734 (x : nadd) : (term204 x) = (term205 x).
Proof. exact (fun_ext (fun y : nadd => @lem1296733 x y)). Qed.
Lemma lem1296735 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1296736 (x : nadd) : (term206 x) = (term207 x).
Proof. exact (MK_COMB (@lem1296735) (@lem1296734 x)). Qed.
Lemma lem1296737 : term208 = term209.
Proof. exact (fun_ext (fun x : nadd => @lem1296736 x)). Qed.
Lemma lem1296738 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1296739 : term210 = term211.
Proof. exact (MK_COMB (@lem1296738) (@lem1296737)). Qed.
Lemma lem1296740 : term211.
Proof. exact (EQ_MP (@lem1296739) (@lem1278498)). Qed.
Lemma lem1296741 (x : nadd) : term212 x.
Proof. exact (@lem1296740 x). Qed.
Lemma lem1296742 (x : nadd) : (term212 x) = (term207 x).
Proof. exact (eq_refl (term212 x)). Qed.
Lemma lem1296743 (x : nadd) : term207 x.
Proof. exact (EQ_MP (@lem1296742 x) (@lem1296741 x)). Qed.
Lemma lem1296744 (x : nadd) (y : nadd) : term213 x y.
Proof. exact (@lem1296743 x y). Qed.
Lemma lem1296745 (x : nadd) (y : nadd) : (term213 x y) = (term203 x y).
Proof. exact (eq_refl (term213 x y)). Qed.
Lemma lem1296746 (x : nadd) (y : nadd) : term203 x y.
Proof. exact (EQ_MP (@lem1296745 x y) (@lem1296744 x y)). Qed.
Lemma lem1296747 (x : nadd) (y : nadd) (z : nadd) : term214 x y z.
Proof. exact (@lem1296746 x y z). Qed.
Lemma lem1296748 (x : nadd) (y : nadd) (z : nadd) : (term214 x y z) = (term197 x y z).
Proof. exact (eq_refl (term214 x y z)). Qed.
Lemma lem1296749 (x : nadd) (y : nadd) (z : nadd) : term197 x y z.
Proof. exact (EQ_MP (@lem1296748 x y z) (@lem1296747 x y z)). Qed.
Lemma lem1296750 (x : nadd) (y : nadd) (z : nadd) : (term197 x y z) = ((term197 x y z) = True).
Proof. exact (@lem7 (term197 x y z)). Qed.
Lemma lem1296752 (h1 : term215) : term215.
Proof. exact (h1). Qed.
Lemma lem1296753 (x : nadd) (h1 : term215) : term216 x.
Proof. exact (@lem1296752 h1 x). Qed.
Lemma lem1296754 (x : nadd) : (term216 x) = (term217 x).
Proof. exact (eq_refl (term216 x)). Qed.
Lemma lem1296755 (x : nadd) (h1 : term215) : term217 x.
Proof. exact (EQ_MP (@lem1296754 x) (@lem1296753 x h1)). Qed.
Lemma lem1296756 (x : nadd) (y : nadd) (h1 : term215) : term218 x y.
Proof. exact (@lem1296755 x h1 y). Qed.
Lemma lem1296757 (y : nadd) (x : nadd) : (term218 x y) = (term219 y x).
Proof. exact (eq_refl (term218 x y)). Qed.
Lemma lem1296758 (y : nadd) (x : nadd) (h1 : term215) : term219 y x.
Proof. exact (EQ_MP (@lem1296757 y x) (@lem1296756 x y h1)). Qed.
Lemma lem1296759 (y : nadd) (x : nadd) (z : nadd) (h1 : term215) : term220 y x z.
Proof. exact (@lem1296758 y x h1 z). Qed.
Lemma lem1296760 (y : nadd) (x : nadd) (z : nadd) : (term220 y x z) = (term221 y x z).
Proof. exact (eq_refl (term220 y x z)). Qed.
Lemma lem1296761 (y : nadd) (x : nadd) (z : nadd) (h1 : term215) : term221 y x z.
Proof. exact (EQ_MP (@lem1296760 y x z) (@lem1296759 y x z h1)). Qed.
Lemma lem1296762 (x : nadd) (y : nadd) (z : nadd) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1296763 (x : nadd) (y : nadd) (z : nadd) (h1 : term215) (h2 : term222 x y z) : nadd_eq x z.
Proof. exact (@lem1296761 y x z h1 (@lem1296762 x y z h2)). Qed.
Lemma lem1296764 (x : nadd) (y : nadd) (z : nadd) (h1 : term222 x y z) : term223 x z.
Proof. exact (fun h0 : term215 => @lem1296763 x y z h0 h1). Qed.
Lemma lem1296765 (x : nadd) (z : nadd) (h1 : term224 x z) : term224 x z.
Proof. exact (h1). Qed.
Lemma lem1296766 (x : nadd) (z : nadd) (h1 : term224 x z) : term223 x z.
Proof. exact (ex_elim (@lem1296765 x z h1) (fun y : nadd => fun h0 : term225 x z y => @lem1296764 x y z h0)). Qed.
Lemma lem1296767 (h1 : term215) : term215.
Proof. exact (h1). Qed.
Lemma lem1296768 (x : nadd) (z : nadd) (h1 : term215) (h2 : term224 x z) : nadd_eq x z.
Proof. exact (@lem1296766 x z h2 (@lem1296767 h1)). Qed.
Lemma lem1296769 (x : nadd) (z : nadd) (h1 : term215) : term226 x z.
Proof. exact (fun h0 : term224 x z => @lem1296768 x z h1 h0). Qed.
Lemma lem1296770 (x : nadd) (h1 : term215) : term227 x.
Proof. exact (fun z : nadd => @lem1296769 x z h1). Qed.
Lemma lem1296771 (h1 : term215) : term228.
Proof. exact (fun x : nadd => @lem1296770 x h1). Qed.
Lemma lem1296772 : term229.
Proof. exact (fun h0 : term215 => @lem1296771 h0). Qed.
Lemma lem1296773 : term228.
Proof. exact (@lem1296772 (@lem1268295)). Qed.
Lemma lem1296774 (x : nadd) : term230 x.
Proof. exact (@lem1296773 x). Qed.
Lemma lem1296775 (x : nadd) : (term230 x) = (term227 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1296776 (x : nadd) : term227 x.
Proof. exact (EQ_MP (@lem1296775 x) (@lem1296774 x)). Qed.
Lemma lem1296777 (x : nadd) (z : nadd) : term231 x z.
Proof. exact (@lem1296776 x z). Qed.
Lemma lem1296778 (x : nadd) (z : nadd) : (term231 x z) = (term226 x z).
Proof. exact (eq_refl (term231 x z)). Qed.
Lemma lem1296780 (x : nadd) : term232 x.
Proof. exact (@lem1278498 x). Qed.
Lemma lem1296781 (x : nadd) : (term232 x) = (term206 x).
Proof. exact (eq_refl (term232 x)). Qed.
Lemma lem1296782 (x : nadd) : term206 x.
Proof. exact (EQ_MP (@lem1296781 x) (@lem1296780 x)). Qed.
Lemma lem1296783 (x : nadd) (y : nadd) : term233 x y.
Proof. exact (@lem1296782 x y). Qed.
Lemma lem1296784 (x : nadd) (y : nadd) : (term233 x y) = (term202 x y).
Proof. exact (eq_refl (term233 x y)). Qed.
Lemma lem1296785 (x : nadd) (y : nadd) : term202 x y.
Proof. exact (EQ_MP (@lem1296784 x y) (@lem1296783 x y)). Qed.
Lemma lem1296786 (x : nadd) (y : nadd) (z : nadd) : term234 x y z.
Proof. exact (@lem1296785 x y z). Qed.
Lemma lem1296787 (x : nadd) (y : nadd) (z : nadd) : (term234 x y z) = (term196 x y z).
Proof. exact (eq_refl (term234 x y z)). Qed.
Lemma lem1296788 (x : nadd) (y : nadd) (z : nadd) : term196 x y z.
Proof. exact (EQ_MP (@lem1296787 x y z) (@lem1296786 x y z)). Qed.
Lemma lem1296789 (x : nadd) (y : nadd) (z : nadd) : (term196 x y z) = ((term196 x y z) = True).
Proof. exact (@lem7 (term196 x y z)). Qed.
Lemma lem1296791 (h1 : term215) : term215.
Proof. exact (h1). Qed.
Lemma lem1296792 (x : nadd) (h1 : term215) : term216 x.
Proof. exact (@lem1296791 h1 x). Qed.
Lemma lem1296793 (x : nadd) : (term216 x) = (term217 x).
Proof. exact (eq_refl (term216 x)). Qed.
Lemma lem1296794 (x : nadd) (h1 : term215) : term217 x.
Proof. exact (EQ_MP (@lem1296793 x) (@lem1296792 x h1)). Qed.
Lemma lem1296795 (x : nadd) (y : nadd) (h1 : term215) : term218 x y.
Proof. exact (@lem1296794 x h1 y). Qed.
Lemma lem1296796 (y : nadd) (x : nadd) : (term218 x y) = (term219 y x).
Proof. exact (eq_refl (term218 x y)). Qed.
Lemma lem1296797 (y : nadd) (x : nadd) (h1 : term215) : term219 y x.
Proof. exact (EQ_MP (@lem1296796 y x) (@lem1296795 x y h1)). Qed.
Lemma lem1296798 (y : nadd) (x : nadd) (z : nadd) (h1 : term215) : term220 y x z.
Proof. exact (@lem1296797 y x h1 z). Qed.
Lemma lem1296799 (y : nadd) (x : nadd) (z : nadd) : (term220 y x z) = (term221 y x z).
Proof. exact (eq_refl (term220 y x z)). Qed.
Lemma lem1296800 (y : nadd) (x : nadd) (z : nadd) (h1 : term215) : term221 y x z.
Proof. exact (EQ_MP (@lem1296799 y x z) (@lem1296798 y x z h1)). Qed.
Lemma lem1296801 (x : nadd) (y : nadd) (z : nadd) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1296802 (x : nadd) (y : nadd) (z : nadd) (h1 : term215) (h2 : term222 x y z) : nadd_eq x z.
Proof. exact (@lem1296800 y x z h1 (@lem1296801 x y z h2)). Qed.
Lemma lem1296803 (x : nadd) (y : nadd) (z : nadd) (h1 : term222 x y z) : term223 x z.
Proof. exact (fun h0 : term215 => @lem1296802 x y z h0 h1). Qed.
Lemma lem1296804 (x : nadd) (z : nadd) (h1 : term224 x z) : term224 x z.
Proof. exact (h1). Qed.
Lemma lem1296805 (x : nadd) (z : nadd) (h1 : term224 x z) : term223 x z.
Proof. exact (ex_elim (@lem1296804 x z h1) (fun y : nadd => fun h0 : term225 x z y => @lem1296803 x y z h0)). Qed.
Lemma lem1296806 (h1 : term215) : term215.
Proof. exact (h1). Qed.
Lemma lem1296807 (x : nadd) (z : nadd) (h1 : term215) (h2 : term224 x z) : nadd_eq x z.
Proof. exact (@lem1296805 x z h2 (@lem1296806 h1)). Qed.
Lemma lem1296808 (x : nadd) (z : nadd) (h1 : term215) : term226 x z.
Proof. exact (fun h0 : term224 x z => @lem1296807 x z h1 h0). Qed.
Lemma lem1296809 (x : nadd) (h1 : term215) : term227 x.
Proof. exact (fun z : nadd => @lem1296808 x z h1). Qed.
Lemma lem1296810 (h1 : term215) : term228.
Proof. exact (fun x : nadd => @lem1296809 x h1). Qed.
Lemma lem1296811 : term229.
Proof. exact (fun h0 : term215 => @lem1296810 h0). Qed.
Lemma lem1296812 : term228.
Proof. exact (@lem1296811 (@lem1268295)). Qed.
Lemma lem1296813 (x : nadd) : term230 x.
Proof. exact (@lem1296812 x). Qed.
Lemma lem1296814 (x : nadd) : (term230 x) = (term227 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1296815 (x : nadd) : term227 x.
Proof. exact (EQ_MP (@lem1296814 x) (@lem1296813 x)). Qed.
Lemma lem1296816 (x : nadd) (z : nadd) : term231 x z.
Proof. exact (@lem1296815 x z). Qed.
Lemma lem1296817 (x : nadd) (z : nadd) : (term231 x z) = (term226 x z).
Proof. exact (eq_refl (term231 x z)). Qed.
Lemma lem1296819 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296820 (x : nadd) (h1 : term150) : term151 x.
Proof. exact (@lem1296819 h1 x). Qed.
Lemma lem1296821 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296822 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (EQ_MP (@lem1296821 x) (@lem1296820 x h1)). Qed.
Lemma lem1296823 (x : nadd) (y : nadd) (h1 : term150) : term153 x y.
Proof. exact (@lem1296822 x h1 y). Qed.
Lemma lem1296824 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296825 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (EQ_MP (@lem1296824 x y) (@lem1296823 x y h1)). Qed.
Lemma lem1296826 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1296827 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296825 x y h1 (@lem1296826 x y h2)). Qed.
Lemma lem1296828 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term155 x y.
Proof. exact (fun h0 : term150 => @lem1296827 x y h0 h1). Qed.
Lemma lem1296829 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296830 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296828 x y h2 (@lem1296829 h1)). Qed.
Lemma lem1296831 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1296830 x y h1 h0). Qed.
Lemma lem1296832 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (fun y : nadd => @lem1296831 x y h1). Qed.
Lemma lem1296833 (h1 : term150) : term150.
Proof. exact (fun x : nadd => @lem1296832 x h1). Qed.
Lemma lem1296834 : term156.
Proof. exact (fun h0 : term150 => @lem1296833 h0). Qed.
Lemma lem1296835 : term150.
Proof. exact (@lem1296834 (@lem1279763)). Qed.
Lemma lem1296836 (x : nadd) : term151 x.
Proof. exact (@lem1296835 x). Qed.
Lemma lem1296837 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296838 (x : nadd) : term152 x.
Proof. exact (EQ_MP (@lem1296837 x) (@lem1296836 x)). Qed.
Lemma lem1296839 (x : nadd) (y : nadd) : term153 x y.
Proof. exact (@lem1296838 x y). Qed.
Lemma lem1296840 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296842 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296843 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296842 h1 x). Qed.
Lemma lem1296844 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296845 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296844 x) (@lem1296843 x h1)). Qed.
Lemma lem1296846 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296845 x h1 y). Qed.
Lemma lem1296847 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296848 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296847 y x) (@lem1296846 x y h1)). Qed.
Lemma lem1296849 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296848 y x h1 z). Qed.
Lemma lem1296850 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296851 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296850 y x z) (@lem1296849 y x z h1)). Qed.
Lemma lem1296852 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296853 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296851 y x z h1 (@lem1296852 x y z h2)). Qed.
Lemma lem1296854 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296853 x y z h0 h1). Qed.
Lemma lem1296855 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296856 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296855 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296854 x y z h0)). Qed.
Lemma lem1296857 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296858 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296856 x z h2 (@lem1296857 h1)). Qed.
Lemma lem1296859 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296858 x z h1 h0). Qed.
Lemma lem1296860 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296859 x z h1). Qed.
Lemma lem1296861 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296860 x h1). Qed.
Lemma lem1296862 : term28.
Proof. exact (fun h0 : term14 => @lem1296861 h0). Qed.
Lemma lem1296863 : term27.
Proof. exact (@lem1296862 (@lem1270880)). Qed.
Lemma lem1296864 (x : nadd) : term29 x.
Proof. exact (@lem1296863 x). Qed.
Lemma lem1296865 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296866 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296865 x) (@lem1296864 x)). Qed.
Lemma lem1296867 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296866 x z). Qed.
Lemma lem1296868 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296870 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296871 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296870 h1 x). Qed.
Lemma lem1296872 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296873 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296872 x) (@lem1296871 x h1)). Qed.
Lemma lem1296874 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296873 x h1 y). Qed.
Lemma lem1296875 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296876 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296875 y x) (@lem1296874 x y h1)). Qed.
Lemma lem1296877 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296876 y x h1 z). Qed.
Lemma lem1296878 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296879 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296878 y x z) (@lem1296877 y x z h1)). Qed.
Lemma lem1296880 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296881 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296879 y x z h1 (@lem1296880 x y z h2)). Qed.
Lemma lem1296882 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296881 x y z h0 h1). Qed.
Lemma lem1296883 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296884 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296883 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296882 x y z h0)). Qed.
Lemma lem1296885 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296886 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296884 x z h2 (@lem1296885 h1)). Qed.
Lemma lem1296887 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296886 x z h1 h0). Qed.
Lemma lem1296888 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296887 x z h1). Qed.
Lemma lem1296889 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296888 x h1). Qed.
Lemma lem1296890 : term28.
Proof. exact (fun h0 : term14 => @lem1296889 h0). Qed.
Lemma lem1296891 : term27.
Proof. exact (@lem1296890 (@lem1270880)). Qed.
Lemma lem1296892 (x : nadd) : term29 x.
Proof. exact (@lem1296891 x). Qed.
Lemma lem1296893 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296894 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296893 x) (@lem1296892 x)). Qed.
Lemma lem1296895 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296894 x z). Qed.
Lemma lem1296896 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296898 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296899 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1296898 h1 x). Qed.
Lemma lem1296900 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1296901 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1296900 x) (@lem1296899 x h1)). Qed.
Lemma lem1296902 (x : nadd) (y : nadd) (h1 : term0) : term3 x y.
Proof. exact (@lem1296901 x h1 y). Qed.
Lemma lem1296903 (y : nadd) (x : nadd) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1296904 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1296903 y x) (@lem1296902 x y h1)). Qed.
Lemma lem1296905 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term5 y x z.
Proof. exact (@lem1296904 y x h1 z). Qed.
Lemma lem1296906 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296907 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1296906 y x z) (@lem1296905 y x z h1)). Qed.
Lemma lem1296908 (y : nadd) (z : nadd) (h1 : nadd_le y z) : nadd_le y z.
Proof. exact (h1). Qed.
Lemma lem1296909 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296907 y x z h1 (@lem1296908 y z h2)). Qed.
Lemma lem1296910 (x : nadd) (y : nadd) (z : nadd) (h1 : nadd_le y z) : term8 y x z.
Proof. exact (fun h0 : term0 => @lem1296909 x y z h0 h1). Qed.
Lemma lem1296911 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1296912 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1296910 x y z h2 (@lem1296911 h1)). Qed.
Lemma lem1296913 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : nadd_le y z => @lem1296912 x y z h1 h0). Qed.
Lemma lem1296914 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (fun z : nadd => @lem1296913 y x z h1). Qed.
Lemma lem1296915 (y : nadd) (h1 : term0) : term9 y.
Proof. exact (fun x : nadd => @lem1296914 y x h1). Qed.
Lemma lem1296916 (h1 : term0) : term10.
Proof. exact (fun y : nadd => @lem1296915 y h1). Qed.
Lemma lem1296917 : term11.
Proof. exact (fun h0 : term0 => @lem1296916 h0). Qed.
Lemma lem1296918 : term10.
Proof. exact (@lem1296917 (@lem1280016)). Qed.
Lemma lem1296919 (y : nadd) : term12 y.
Proof. exact (@lem1296918 y). Qed.
Lemma lem1296920 (y : nadd) : (term12 y) = (term9 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem1296921 (y : nadd) : term9 y.
Proof. exact (EQ_MP (@lem1296920 y) (@lem1296919 y)). Qed.
Lemma lem1296922 (y : nadd) (x : nadd) : term13 y x.
Proof. exact (@lem1296921 y x). Qed.
Lemma lem1296923 (y : nadd) (x : nadd) : (term13 y x) = (term4 y x).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1296924 (y : nadd) (x : nadd) : term4 y x.
Proof. exact (EQ_MP (@lem1296923 y x) (@lem1296922 y x)). Qed.
Lemma lem1296925 (y : nadd) (x : nadd) (z : nadd) : term5 y x z.
Proof. exact (@lem1296924 y x z). Qed.
Lemma lem1296926 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1296928 (x : nadd) : term193 x.
Proof. exact (@lem1268060 x). Qed.
Lemma lem1296929 (x : nadd) : (term193 x) = (term194 x).
Proof. exact (eq_refl (term193 x)). Qed.
Lemma lem1296930 (x : nadd) : term194 x.
Proof. exact (EQ_MP (@lem1296929 x) (@lem1296928 x)). Qed.
Lemma lem1296931 (x : nadd) (y : nadd) : term195 x y.
Proof. exact (@lem1296930 x y). Qed.
Lemma lem1296932 (y : nadd) (x : nadd) : (term195 x y) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1296934 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296935 (x : nadd) (h1 : term150) : term151 x.
Proof. exact (@lem1296934 h1 x). Qed.
Lemma lem1296936 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296937 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (EQ_MP (@lem1296936 x) (@lem1296935 x h1)). Qed.
Lemma lem1296938 (x : nadd) (y : nadd) (h1 : term150) : term153 x y.
Proof. exact (@lem1296937 x h1 y). Qed.
Lemma lem1296939 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296940 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (EQ_MP (@lem1296939 x y) (@lem1296938 x y h1)). Qed.
Lemma lem1296941 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1296942 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296940 x y h1 (@lem1296941 x y h2)). Qed.
Lemma lem1296943 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term155 x y.
Proof. exact (fun h0 : term150 => @lem1296942 x y h0 h1). Qed.
Lemma lem1296944 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1296945 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1296943 x y h2 (@lem1296944 h1)). Qed.
Lemma lem1296946 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1296945 x y h1 h0). Qed.
Lemma lem1296947 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (fun y : nadd => @lem1296946 x y h1). Qed.
Lemma lem1296948 (h1 : term150) : term150.
Proof. exact (fun x : nadd => @lem1296947 x h1). Qed.
Lemma lem1296949 : term156.
Proof. exact (fun h0 : term150 => @lem1296948 h0). Qed.
Lemma lem1296950 : term150.
Proof. exact (@lem1296949 (@lem1279763)). Qed.
Lemma lem1296951 (x : nadd) : term151 x.
Proof. exact (@lem1296950 x). Qed.
Lemma lem1296952 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1296953 (x : nadd) : term152 x.
Proof. exact (EQ_MP (@lem1296952 x) (@lem1296951 x)). Qed.
Lemma lem1296954 (x : nadd) (y : nadd) : term153 x y.
Proof. exact (@lem1296953 x y). Qed.
Lemma lem1296955 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1296957 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296958 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296957 h1 x). Qed.
Lemma lem1296959 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296960 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296959 x) (@lem1296958 x h1)). Qed.
Lemma lem1296961 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296960 x h1 y). Qed.
Lemma lem1296962 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296963 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296962 y x) (@lem1296961 x y h1)). Qed.
Lemma lem1296964 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296963 y x h1 z). Qed.
Lemma lem1296965 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296966 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296965 y x z) (@lem1296964 y x z h1)). Qed.
Lemma lem1296967 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296968 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296966 y x z h1 (@lem1296967 x y z h2)). Qed.
Lemma lem1296969 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296968 x y z h0 h1). Qed.
Lemma lem1296970 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296971 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296970 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296969 x y z h0)). Qed.
Lemma lem1296972 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296973 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296971 x z h2 (@lem1296972 h1)). Qed.
Lemma lem1296974 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1296973 x z h1 h0). Qed.
Lemma lem1296975 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1296974 x z h1). Qed.
Lemma lem1296976 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1296975 x h1). Qed.
Lemma lem1296977 : term28.
Proof. exact (fun h0 : term14 => @lem1296976 h0). Qed.
Lemma lem1296978 : term27.
Proof. exact (@lem1296977 (@lem1270880)). Qed.
Lemma lem1296979 (x : nadd) : term29 x.
Proof. exact (@lem1296978 x). Qed.
Lemma lem1296980 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1296981 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1296980 x) (@lem1296979 x)). Qed.
Lemma lem1296982 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1296981 x z). Qed.
Lemma lem1296983 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1296985 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1296986 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1296985 h1 x). Qed.
Lemma lem1296987 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1296988 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1296987 x) (@lem1296986 x h1)). Qed.
Lemma lem1296989 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1296988 x h1 y). Qed.
Lemma lem1296990 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1296991 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1296990 y x) (@lem1296989 x y h1)). Qed.
Lemma lem1296992 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1296991 y x h1 z). Qed.
Lemma lem1296993 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1296994 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1296993 y x z) (@lem1296992 y x z h1)). Qed.
Lemma lem1296995 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1296996 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1296994 y x z h1 (@lem1296995 x y z h2)). Qed.
Lemma lem1296997 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1296996 x y z h0 h1). Qed.
Lemma lem1296998 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1296999 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1296998 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1296997 x y z h0)). Qed.
Lemma lem1297000 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297001 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1296999 x z h2 (@lem1297000 h1)). Qed.
Lemma lem1297002 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1297001 x z h1 h0). Qed.
Lemma lem1297003 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1297002 x z h1). Qed.
Lemma lem1297004 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1297003 x h1). Qed.
Lemma lem1297005 : term28.
Proof. exact (fun h0 : term14 => @lem1297004 h0). Qed.
Lemma lem1297006 : term27.
Proof. exact (@lem1297005 (@lem1270880)). Qed.
Lemma lem1297007 (x : nadd) : term29 x.
Proof. exact (@lem1297006 x). Qed.
Lemma lem1297008 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1297009 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1297008 x) (@lem1297007 x)). Qed.
Lemma lem1297010 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1297009 x z). Qed.
Lemma lem1297011 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1297015 (m : nat) (n : nat) (h1 : (term235 m n) = (Peano.le m n)) : (term235 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem1297016 (m : nat) (n : nat) (h1 : (term235 m n) = (Peano.le m n)) : (Peano.le m n) = (term235 m n).
Proof. exact (SYM (@lem1297015 m n h1)). Qed.
Lemma lem1297017 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term235 m n)) : (Peano.le m n) = (term235 m n).
Proof. exact (h1). Qed.
Lemma lem1297018 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term235 m n)) : (term235 m n) = (Peano.le m n).
Proof. exact (SYM (@lem1297017 m n h1)). Qed.
Lemma lem1297019 (m : nat) (n : nat) : ((term235 m n) = (Peano.le m n)) = ((Peano.le m n) = (term235 m n)).
Proof. exact (prop_ext (fun h1 : (term235 m n) = (Peano.le m n) => @lem1297016 m n h1) (fun h1 : (Peano.le m n) = (term235 m n) => @lem1297018 m n h1)). Qed.
Lemma lem1297020 (m : nat) : (term236 m) = (term237 m).
Proof. exact (fun_ext (fun n : nat => @lem1297019 m n)). Qed.
Lemma lem1297021 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297022 (m : nat) : (term238 m) = (term239 m).
Proof. exact (MK_COMB (@lem1297021) (@lem1297020 m)). Qed.
Lemma lem1297023 : term240 = term241.
Proof. exact (fun_ext (fun m : nat => @lem1297022 m)). Qed.
Lemma lem1297024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297025 : term242 = term243.
Proof. exact (MK_COMB (@lem1297024) (@lem1297023)). Qed.
Lemma lem1297026 : term243.
Proof. exact (EQ_MP (@lem1297025) (@lem1273281)). Qed.
Lemma lem1297027 (m : nat) : term244 m.
Proof. exact (@lem1297026 m). Qed.
Lemma lem1297028 (m : nat) : (term244 m) = (term239 m).
Proof. exact (eq_refl (term244 m)). Qed.
Lemma lem1297029 (m : nat) : term239 m.
Proof. exact (EQ_MP (@lem1297028 m) (@lem1297027 m)). Qed.
Lemma lem1297030 (m : nat) (n : nat) : term245 m n.
Proof. exact (@lem1297029 m n). Qed.
Lemma lem1297031 (m : nat) (n : nat) : (term245 m n) = ((Peano.le m n) = (term235 m n)).
Proof. exact (eq_refl (term245 m n)). Qed.
Lemma lem1297033 (n : nat) (x : nadd) : term246 n x.
Proof. exact (@lem1273055 (term247 n x)). Qed.
Lemma lem1297034 (n : nat) (x : nadd) : (term246 n x) = (term248 n x).
Proof. exact (eq_refl (term246 n x)). Qed.
Lemma lem1297035 (n : nat) (x : nadd) : term248 n x.
Proof. exact (EQ_MP (@lem1297034 n x) (@lem1297033 n x)). Qed.
Lemma lem1297036 (x : nadd) (r : nat -> nat) (n : nat) : term249 x r n.
Proof. exact (@lem1297035 n x (term250 r n)). Qed.
Lemma lem1297037 (r : nat -> nat) (n : nat) (x : nadd) : (term249 x r n) = (term251 r n x).
Proof. exact (eq_refl (term249 x r n)). Qed.
Lemma lem1297038 (r : nat -> nat) (n : nat) (x : nadd) : term251 r n x.
Proof. exact (EQ_MP (@lem1297037 r n x) (@lem1297036 x r n)). Qed.
Lemma lem1297054 (a : Prop) (c : Prop) (b : Prop) (h1 : term252 a c b) : term252 a c b.
Proof. exact (h1). Qed.
Lemma lem1297055 (c : Prop) (h1 : c) : c.
Proof. exact (h1). Qed.
Lemma lem1297056 (a : Prop) (c : Prop) (b : Prop) (h1 : term252 a c b) : term253 c b.
Proof. exact (proj2 (@lem1297054 a c b h1)). Qed.
Lemma lem1297057 (a : Prop) (c : Prop) (b : Prop) (h1 : term252 a c b) : a \/ b.
Proof. exact (proj1 (@lem1297054 a c b h1)). Qed.
Lemma lem1297058 (c : Prop) (b : Prop) : (c /\ b) = (c /\ b).
Proof. exact (eq_refl (c /\ b)). Qed.
Lemma lem1297059 (c : Prop) (b : Prop) : (term253 c b) = (term254 c b).
Proof. exact (MK_COMB (@lem56) (@lem1297058 c b)). Qed.
Lemma lem1297060 (c : Prop) (b : Prop) : (term254 c b) = (term255 c b).
Proof. exact (eq_refl (term254 c b)). Qed.
Lemma lem1297061 (c : Prop) (b : Prop) : (term256 c b) = (term256 c b).
Proof. exact (eq_refl (term256 c b)). Qed.
Lemma lem1297062 (c : Prop) (b : Prop) : ((term253 c b) = (term254 c b)) = ((term253 c b) = (term255 c b)).
Proof. exact (MK_COMB (@lem1297061 c b) (@lem1297060 c b)). Qed.
Lemma lem1297063 (c : Prop) (b : Prop) : (term253 c b) = (term255 c b).
Proof. exact (EQ_MP (@lem1297062 c b) (@lem1297059 c b)). Qed.
Lemma lem1297064 (a : Prop) (c : Prop) (b : Prop) (h1 : term252 a c b) : term255 c b.
Proof. exact (EQ_MP (@lem1297063 c b) (@lem1297056 a c b h1)). Qed.
Lemma lem1297065 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem1297066 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem1297067 (c : Prop) (b : Prop) (h1 : c /\ b) : c /\ b.
Proof. exact (h1). Qed.
Lemma lem1297068 (a : Prop) (c : Prop) (b : Prop) (h1 : c /\ b) (h2 : term252 a c b) : False.
Proof. exact (@lem1297064 a c b h2 (@lem1297067 c b h1)). Qed.
Lemma lem1297069 (b : Prop) (c : Prop) (h1 : b) (h2 : c) : c /\ b.
Proof. exact (conj (@lem1297055 c h2) (@lem1297066 b h1)). Qed.
Lemma lem1297070 (a : Prop) (h1 : False) : a.
Proof. exact (@lem98 a h1). Qed.
Lemma lem1297071 (a : Prop) (c : Prop) (b : Prop) (h1 : c /\ b) (h2 : term252 a c b) : False = a.
Proof. exact (prop_ext (fun h3 : False => @lem1297070 a h3) (fun h3 : a => @lem1297068 a c b h1 h2)). Qed.
Lemma lem1297072 (a : Prop) (c : Prop) (b : Prop) (h1 : c /\ b) (h2 : term252 a c b) : a.
Proof. exact (EQ_MP (@lem1297071 a c b h1 h2) (@lem1297068 a c b h1 h2)). Qed.
Lemma lem1297073 (a : Prop) (c : Prop) (b : Prop) (h1 : b) (h2 : c) (h3 : term252 a c b) : (c /\ b) = a.
Proof. exact (prop_ext (fun h4 : c /\ b => @lem1297072 a c b h4 h3) (fun h4 : a => @lem1297069 b c h1 h2)). Qed.
Lemma lem1297074 (a : Prop) (c : Prop) (b : Prop) (h1 : b) (h2 : c) (h3 : term252 a c b) : a.
Proof. exact (EQ_MP (@lem1297073 a c b h1 h2 h3) (@lem1297069 b c h1 h2)). Qed.
Lemma lem1297075 (a : Prop) (c : Prop) (b : Prop) (h1 : c) (h2 : term252 a c b) : a.
Proof. exact (or_elim (@lem1297057 a c b h2) (fun h0 : a => @lem1297065 a h0) (fun h0 : b => @lem1297074 a c b h0 h1 h2)). Qed.
Lemma lem1297076 (a : Prop) (c : Prop) (b : Prop) (h1 : term252 a c b) : c -> a.
Proof. exact (fun h0 : c => @lem1297075 a c b h0 h1). Qed.
Lemma lem1297078 {A : Type'} (P : A -> Prop) : term257 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem1297079 {A : Type'} (P : A -> Prop) : (term257 A P) = ((term258 A P) = (term259 A P)).
Proof. exact (eq_refl (term257 A P)). Qed.
Lemma lem1297081 (n : nat) : term260 n.
Proof. exact (@lem91686 n). Qed.
Lemma lem1297082 (n : nat) : (term260 n) = (term261 n).
Proof. exact (eq_refl (term260 n)). Qed.
Lemma lem1297083 (n : nat) : term261 n.
Proof. exact (EQ_MP (@lem1297082 n) (@lem1297081 n)). Qed.
Lemma lem1297084 (n : nat) : term262 n.
Proof. exact (@lem82 (Peano.lt n n)). Qed.
Lemma lem1297086 (m : nat) : term263 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem1297087 (m : nat) : (term263 m) = (term264 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem1297088 (m : nat) : term264 m.
Proof. exact (EQ_MP (@lem1297087 m) (@lem1297086 m)). Qed.
Lemma lem1297089 (m : nat) (n : nat) : term265 m n.
Proof. exact (@lem1297088 m n). Qed.
Lemma lem1297090 (m : nat) (n : nat) : (term265 m n) = ((term266 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term265 m n)). Qed.
Lemma lem1297092 {A B : Type'} (P : type1413 A B) : term267 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1297093 {A B : Type'} (P : type1413 A B) : (term267 A B P) = ((term268 A B P) = (term269 A B P)).
Proof. exact (eq_refl (term267 A B P)). Qed.
Lemma lem1297095 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1297096 (x : nadd) (h1 : term150) : term151 x.
Proof. exact (@lem1297095 h1 x). Qed.
Lemma lem1297097 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1297098 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (EQ_MP (@lem1297097 x) (@lem1297096 x h1)). Qed.
Lemma lem1297099 (x : nadd) (y : nadd) (h1 : term150) : term153 x y.
Proof. exact (@lem1297098 x h1 y). Qed.
Lemma lem1297100 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1297101 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (EQ_MP (@lem1297100 x y) (@lem1297099 x y h1)). Qed.
Lemma lem1297102 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1297103 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1297101 x y h1 (@lem1297102 x y h2)). Qed.
Lemma lem1297104 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term155 x y.
Proof. exact (fun h0 : term150 => @lem1297103 x y h0 h1). Qed.
Lemma lem1297105 (h1 : term150) : term150.
Proof. exact (h1). Qed.
Lemma lem1297106 (x : nadd) (y : nadd) (h1 : term150) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1297104 x y h2 (@lem1297105 h1)). Qed.
Lemma lem1297107 (x : nadd) (y : nadd) (h1 : term150) : term154 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1297106 x y h1 h0). Qed.
Lemma lem1297108 (x : nadd) (h1 : term150) : term152 x.
Proof. exact (fun y : nadd => @lem1297107 x y h1). Qed.
Lemma lem1297109 (h1 : term150) : term150.
Proof. exact (fun x : nadd => @lem1297108 x h1). Qed.
Lemma lem1297110 : term156.
Proof. exact (fun h0 : term150 => @lem1297109 h0). Qed.
Lemma lem1297111 : term150.
Proof. exact (@lem1297110 (@lem1279763)). Qed.
Lemma lem1297112 (x : nadd) : term151 x.
Proof. exact (@lem1297111 x). Qed.
Lemma lem1297113 (x : nadd) : (term151 x) = (term152 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1297114 (x : nadd) : term152 x.
Proof. exact (EQ_MP (@lem1297113 x) (@lem1297112 x)). Qed.
Lemma lem1297115 (x : nadd) (y : nadd) : term153 x y.
Proof. exact (@lem1297114 x y). Qed.
Lemma lem1297116 (x : nadd) (y : nadd) : (term153 x y) = (term154 x y).
Proof. exact (eq_refl (term153 x y)). Qed.
Lemma lem1297118 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297119 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1297118 h1 x). Qed.
Lemma lem1297120 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1297121 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1297120 x) (@lem1297119 x h1)). Qed.
Lemma lem1297122 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1297121 x h1 y). Qed.
Lemma lem1297123 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1297124 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1297123 y x) (@lem1297122 x y h1)). Qed.
Lemma lem1297125 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1297124 y x h1 z). Qed.
Lemma lem1297126 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1297127 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1297126 y x z) (@lem1297125 y x z h1)). Qed.
Lemma lem1297128 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1297129 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1297127 y x z h1 (@lem1297128 x y z h2)). Qed.
Lemma lem1297130 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1297129 x y z h0 h1). Qed.
Lemma lem1297131 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1297132 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1297131 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1297130 x y z h0)). Qed.
Lemma lem1297133 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297134 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1297132 x z h2 (@lem1297133 h1)). Qed.
Lemma lem1297135 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1297134 x z h1 h0). Qed.
Lemma lem1297136 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1297135 x z h1). Qed.
Lemma lem1297137 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1297136 x h1). Qed.
Lemma lem1297138 : term28.
Proof. exact (fun h0 : term14 => @lem1297137 h0). Qed.
Lemma lem1297139 : term27.
Proof. exact (@lem1297138 (@lem1270880)). Qed.
Lemma lem1297140 (x : nadd) : term29 x.
Proof. exact (@lem1297139 x). Qed.
Lemma lem1297141 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1297142 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1297141 x) (@lem1297140 x)). Qed.
Lemma lem1297143 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1297142 x z). Qed.
Lemma lem1297144 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1297146 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1297147 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1297146 h1 x). Qed.
Lemma lem1297148 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1297149 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1297148 x) (@lem1297147 x h1)). Qed.
Lemma lem1297150 (x : nadd) (y : nadd) (h1 : term0) : term3 x y.
Proof. exact (@lem1297149 x h1 y). Qed.
Lemma lem1297151 (y : nadd) (x : nadd) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1297152 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1297151 y x) (@lem1297150 x y h1)). Qed.
Lemma lem1297153 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term5 y x z.
Proof. exact (@lem1297152 y x h1 z). Qed.
Lemma lem1297154 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1297155 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1297154 y x z) (@lem1297153 y x z h1)). Qed.
Lemma lem1297156 (y : nadd) (z : nadd) (h1 : nadd_le y z) : nadd_le y z.
Proof. exact (h1). Qed.
Lemma lem1297157 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1297155 y x z h1 (@lem1297156 y z h2)). Qed.
Lemma lem1297158 (x : nadd) (y : nadd) (z : nadd) (h1 : nadd_le y z) : term8 y x z.
Proof. exact (fun h0 : term0 => @lem1297157 x y z h0 h1). Qed.
Lemma lem1297159 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1297160 (x : nadd) (y : nadd) (z : nadd) (h1 : term0) (h2 : nadd_le y z) : term7 y x z.
Proof. exact (@lem1297158 x y z h2 (@lem1297159 h1)). Qed.
Lemma lem1297161 (y : nadd) (x : nadd) (z : nadd) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : nadd_le y z => @lem1297160 x y z h1 h0). Qed.
Lemma lem1297162 (y : nadd) (x : nadd) (h1 : term0) : term4 y x.
Proof. exact (fun z : nadd => @lem1297161 y x z h1). Qed.
Lemma lem1297163 (y : nadd) (h1 : term0) : term9 y.
Proof. exact (fun x : nadd => @lem1297162 y x h1). Qed.
Lemma lem1297164 (h1 : term0) : term10.
Proof. exact (fun y : nadd => @lem1297163 y h1). Qed.
Lemma lem1297165 : term11.
Proof. exact (fun h0 : term0 => @lem1297164 h0). Qed.
Lemma lem1297166 : term10.
Proof. exact (@lem1297165 (@lem1280016)). Qed.
Lemma lem1297167 (y : nadd) : term12 y.
Proof. exact (@lem1297166 y). Qed.
Lemma lem1297168 (y : nadd) : (term12 y) = (term9 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem1297169 (y : nadd) : term9 y.
Proof. exact (EQ_MP (@lem1297168 y) (@lem1297167 y)). Qed.
Lemma lem1297170 (y : nadd) (x : nadd) : term13 y x.
Proof. exact (@lem1297169 y x). Qed.
Lemma lem1297171 (y : nadd) (x : nadd) : (term13 y x) = (term4 y x).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1297172 (y : nadd) (x : nadd) : term4 y x.
Proof. exact (EQ_MP (@lem1297171 y x) (@lem1297170 y x)). Qed.
Lemma lem1297173 (y : nadd) (x : nadd) (z : nadd) : term5 y x z.
Proof. exact (@lem1297172 y x z). Qed.
Lemma lem1297174 (y : nadd) (x : nadd) (z : nadd) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1297176 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297177 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1297176 h1 x). Qed.
Lemma lem1297178 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1297179 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1297178 x) (@lem1297177 x h1)). Qed.
Lemma lem1297180 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1297179 x h1 y). Qed.
Lemma lem1297181 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1297182 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1297181 y x) (@lem1297180 x y h1)). Qed.
Lemma lem1297183 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1297182 y x h1 z). Qed.
Lemma lem1297184 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1297185 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1297184 y x z) (@lem1297183 y x z h1)). Qed.
Lemma lem1297186 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1297187 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1297185 y x z h1 (@lem1297186 x y z h2)). Qed.
Lemma lem1297188 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1297187 x y z h0 h1). Qed.
Lemma lem1297189 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1297190 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1297189 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1297188 x y z h0)). Qed.
Lemma lem1297191 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297192 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1297190 x z h2 (@lem1297191 h1)). Qed.
Lemma lem1297193 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1297192 x z h1 h0). Qed.
Lemma lem1297194 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1297193 x z h1). Qed.
Lemma lem1297195 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1297194 x h1). Qed.
Lemma lem1297196 : term28.
Proof. exact (fun h0 : term14 => @lem1297195 h0). Qed.
Lemma lem1297197 : term27.
Proof. exact (@lem1297196 (@lem1270880)). Qed.
Lemma lem1297198 (x : nadd) : term29 x.
Proof. exact (@lem1297197 x). Qed.
Lemma lem1297199 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1297200 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1297199 x) (@lem1297198 x)). Qed.
Lemma lem1297201 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1297200 x z). Qed.
Lemma lem1297202 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1297204 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297205 (x : nadd) (h1 : term14) : term15 x.
Proof. exact (@lem1297204 h1 x). Qed.
Lemma lem1297206 (x : nadd) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1297207 (x : nadd) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1297206 x) (@lem1297205 x h1)). Qed.
Lemma lem1297208 (x : nadd) (y : nadd) (h1 : term14) : term17 x y.
Proof. exact (@lem1297207 x h1 y). Qed.
Lemma lem1297209 (y : nadd) (x : nadd) : (term17 x y) = (term18 y x).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1297210 (y : nadd) (x : nadd) (h1 : term14) : term18 y x.
Proof. exact (EQ_MP (@lem1297209 y x) (@lem1297208 x y h1)). Qed.
Lemma lem1297211 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term19 y x z.
Proof. exact (@lem1297210 y x h1 z). Qed.
Lemma lem1297212 (y : nadd) (x : nadd) (z : nadd) : (term19 y x z) = (term20 y x z).
Proof. exact (eq_refl (term19 y x z)). Qed.
Lemma lem1297213 (y : nadd) (x : nadd) (z : nadd) (h1 : term14) : term20 y x z.
Proof. exact (EQ_MP (@lem1297212 y x z) (@lem1297211 y x z h1)). Qed.
Lemma lem1297214 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1297215 (x : nadd) (y : nadd) (z : nadd) (h1 : term14) (h2 : term21 x y z) : nadd_le x z.
Proof. exact (@lem1297213 y x z h1 (@lem1297214 x y z h2)). Qed.
Lemma lem1297216 (x : nadd) (y : nadd) (z : nadd) (h1 : term21 x y z) : term22 x z.
Proof. exact (fun h0 : term14 => @lem1297215 x y z h0 h1). Qed.
Lemma lem1297217 (x : nadd) (z : nadd) (h1 : term23 x z) : term23 x z.
Proof. exact (h1). Qed.
Lemma lem1297218 (x : nadd) (z : nadd) (h1 : term23 x z) : term22 x z.
Proof. exact (ex_elim (@lem1297217 x z h1) (fun y : nadd => fun h0 : term24 x z y => @lem1297216 x y z h0)). Qed.
Lemma lem1297219 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1297220 (x : nadd) (z : nadd) (h1 : term14) (h2 : term23 x z) : nadd_le x z.
Proof. exact (@lem1297218 x z h2 (@lem1297219 h1)). Qed.
Lemma lem1297221 (x : nadd) (z : nadd) (h1 : term14) : term25 x z.
Proof. exact (fun h0 : term23 x z => @lem1297220 x z h1 h0). Qed.
Lemma lem1297222 (x : nadd) (h1 : term14) : term26 x.
Proof. exact (fun z : nadd => @lem1297221 x z h1). Qed.
Lemma lem1297223 (h1 : term14) : term27.
Proof. exact (fun x : nadd => @lem1297222 x h1). Qed.
Lemma lem1297224 : term28.
Proof. exact (fun h0 : term14 => @lem1297223 h0). Qed.
Lemma lem1297225 : term27.
Proof. exact (@lem1297224 (@lem1270880)). Qed.
Lemma lem1297226 (x : nadd) : term29 x.
Proof. exact (@lem1297225 x). Qed.
Lemma lem1297227 (x : nadd) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1297228 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1297227 x) (@lem1297226 x)). Qed.
Lemma lem1297229 (x : nadd) (z : nadd) : term30 x z.
Proof. exact (@lem1297228 x z). Qed.
Lemma lem1297230 (x : nadd) (z : nadd) : (term30 x z) = (term25 x z).
Proof. exact (eq_refl (term30 x z)). Qed.
Lemma lem1297234 (m : nat) (n : nat) (h1 : (term235 m n) = (Peano.le m n)) : (term235 m n) = (Peano.le m n).
Proof. exact (h1). Qed.
Lemma lem1297235 (m : nat) (n : nat) (h1 : (term235 m n) = (Peano.le m n)) : (Peano.le m n) = (term235 m n).
Proof. exact (SYM (@lem1297234 m n h1)). Qed.
Lemma lem1297236 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term235 m n)) : (Peano.le m n) = (term235 m n).
Proof. exact (h1). Qed.
Lemma lem1297237 (m : nat) (n : nat) (h1 : (Peano.le m n) = (term235 m n)) : (term235 m n) = (Peano.le m n).
Proof. exact (SYM (@lem1297236 m n h1)). Qed.
Lemma lem1297238 (m : nat) (n : nat) : ((term235 m n) = (Peano.le m n)) = ((Peano.le m n) = (term235 m n)).
Proof. exact (prop_ext (fun h1 : (term235 m n) = (Peano.le m n) => @lem1297235 m n h1) (fun h1 : (Peano.le m n) = (term235 m n) => @lem1297237 m n h1)). Qed.
Lemma lem1297239 (m : nat) : (term236 m) = (term237 m).
Proof. exact (fun_ext (fun n : nat => @lem1297238 m n)). Qed.
Lemma lem1297240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297241 (m : nat) : (term238 m) = (term239 m).
Proof. exact (MK_COMB (@lem1297240) (@lem1297239 m)). Qed.
Lemma lem1297242 : term240 = term241.
Proof. exact (fun_ext (fun m : nat => @lem1297241 m)). Qed.
Lemma lem1297243 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297244 : term242 = term243.
Proof. exact (MK_COMB (@lem1297243) (@lem1297242)). Qed.
Lemma lem1297245 : term243.
Proof. exact (EQ_MP (@lem1297244) (@lem1273281)). Qed.
Lemma lem1297246 (m : nat) : term244 m.
Proof. exact (@lem1297245 m). Qed.
Lemma lem1297247 (m : nat) : (term244 m) = (term239 m).
Proof. exact (eq_refl (term244 m)). Qed.
Lemma lem1297248 (m : nat) : term239 m.
Proof. exact (EQ_MP (@lem1297247 m) (@lem1297246 m)). Qed.
Lemma lem1297249 (m : nat) (n : nat) : term245 m n.
Proof. exact (@lem1297248 m n). Qed.
Lemma lem1297250 (m : nat) (n : nat) : (term245 m n) = ((Peano.le m n) = (term235 m n)).
Proof. exact (eq_refl (term245 m n)). Qed.
Lemma lem1297252 (m : nadd) : term270 m.
Proof. exact (@lem1273144 m). Qed.
Lemma lem1297253 (m : nadd) : (term270 m) = (term271 m).
Proof. exact (eq_refl (term270 m)). Qed.
Lemma lem1297254 (m : nadd) : term271 m.
Proof. exact (EQ_MP (@lem1297253 m) (@lem1297252 m)). Qed.
Lemma lem1297255 (m : nadd) (N : nat) (h1 : term272 m N) : term272 m N.
Proof. exact (h1). Qed.
Lemma lem1297257 (P : nat -> Prop) (h1 : (term273 P) = (term274 P)) : (term273 P) = (term274 P).
Proof. exact (h1). Qed.
Lemma lem1297258 (P : nat -> Prop) (h1 : (term273 P) = (term274 P)) : (term274 P) = (term273 P).
Proof. exact (SYM (@lem1297257 P h1)). Qed.
Lemma lem1297259 (P : nat -> Prop) (h1 : (term274 P) = (term273 P)) : (term274 P) = (term273 P).
Proof. exact (h1). Qed.
Lemma lem1297260 (P : nat -> Prop) (h1 : (term274 P) = (term273 P)) : (term273 P) = (term274 P).
Proof. exact (SYM (@lem1297259 P h1)). Qed.
Lemma lem1297261 (P : nat -> Prop) : ((term273 P) = (term274 P)) = ((term274 P) = (term273 P)).
Proof. exact (prop_ext (fun h1 : (term273 P) = (term274 P) => @lem1297258 P h1) (fun h1 : (term274 P) = (term273 P) => @lem1297260 P h1)). Qed.
Lemma lem1297262 : term275 = term276.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem1297261 P)). Qed.
Lemma lem1297263 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem1297264 : term277 = term278.
Proof. exact (MK_COMB (@lem1297263) (@lem1297262)). Qed.
Lemma lem1297265 : term278.
Proof. exact (EQ_MP (@lem1297264) (@lem117739)). Qed.
Lemma lem1297266 (P : nat -> Prop) : term279 P.
Proof. exact (@lem1297265 P). Qed.
Lemma lem1297267 (P : nat -> Prop) : (term279 P) = ((term274 P) = (term273 P)).
Proof. exact (eq_refl (term279 P)). Qed.
Lemma lem1297269 (P : nadd -> Prop) (h1 : term280 P) : term280 P.
Proof. exact (h1). Qed.
Lemma lem1297270 (P : nadd -> Prop) (h1 : term281 P) : term281 P.
Proof. exact (h1). Qed.
Lemma lem1297271 (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term282 P m.
Proof. exact (h1). Qed.
Lemma lem1297272 (P : nadd -> Prop) (h1 : term283 P) : term283 P.
Proof. exact (h1). Qed.
Lemma lem1297273 (P : nadd -> Prop) (a : nadd) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem1297274 (P : nadd -> Prop) (h1 : term284 P) : term284 P.
Proof. exact (h1). Qed.
Lemma lem1297276 (P : nat -> Prop) : (term274 P) = (term273 P).
Proof. exact (EQ_MP (@lem1297267 P) (@lem1297266 P)). Qed.
Lemma lem1297277 (P : nadd -> Prop) (n : nat) : (term285 P n) = (term286 P n).
Proof. exact (@lem1297276 (term287 P n)). Qed.
Lemma lem1297278 (P : nadd -> Prop) (r : nat) (n : nat) : (term288 P n r) = (term289 P r n).
Proof. exact (eq_refl (term288 P n r)). Qed.
Lemma lem1297279 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297280 (P : nadd -> Prop) (r : nat) (n : nat) : (term290 P n r) = (term291 P r n).
Proof. exact (MK_COMB (@lem1297279) (@lem1297278 P r n)). Qed.
Lemma lem1297281 (P : nadd -> Prop) (r' : nat) (n : nat) : (term288 P n r') = (term289 P r' n).
Proof. exact (eq_refl (term288 P n r')). Qed.
Lemma lem1297282 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1297283 (P : nadd -> Prop) (r' : nat) (n : nat) : (term292 P n r') = (term293 P r' n).
Proof. exact (MK_COMB (@lem1297282) (@lem1297281 P r' n)). Qed.
Lemma lem1297284 (r' : nat) (r : nat) : (Peano.le r' r) = (Peano.le r' r).
Proof. exact (eq_refl (Peano.le r' r)). Qed.
Lemma lem1297285 (P : nadd -> Prop) (n : nat) (r' : nat) (r : nat) : (term294 P n r' r) = (term295 P n r' r).
Proof. exact (MK_COMB (@lem1297283 P r' n) (@lem1297284 r' r)). Qed.
Lemma lem1297286 (P : nadd -> Prop) (n : nat) (r : nat) : (term296 P n r) = (term297 P n r).
Proof. exact (fun_ext (fun r' : nat => @lem1297285 P n r' r)). Qed.
Lemma lem1297287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297288 (P : nadd -> Prop) (n : nat) (r : nat) : (term298 P n r) = (term299 P n r).
Proof. exact (MK_COMB (@lem1297287) (@lem1297286 P n r)). Qed.
Lemma lem1297289 (P : nadd -> Prop) (n : nat) (r : nat) : (term300 P n r) = (term301 P n r).
Proof. exact (MK_COMB (@lem1297280 P r n) (@lem1297288 P n r)). Qed.
Lemma lem1297290 (P : nadd -> Prop) (n : nat) : (term302 P n) = (term303 P n).
Proof. exact (fun_ext (fun r : nat => @lem1297289 P n r)). Qed.
Lemma lem1297291 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1297292 (P : nadd -> Prop) (n : nat) : (term285 P n) = (term304 P n).
Proof. exact (MK_COMB (@lem1297291) (@lem1297290 P n)). Qed.
Lemma lem1297293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1297294 (P : nadd -> Prop) (n : nat) : (term305 P n) = (term306 P n).
Proof. exact (MK_COMB (@lem1297293) (@lem1297292 P n)). Qed.
Lemma lem1297295 (P : nadd -> Prop) (r' : nat) (n : nat) : (term288 P n r') = (term289 P r' n).
Proof. exact (eq_refl (term288 P n r')). Qed.
Lemma lem1297296 (P : nadd -> Prop) (n : nat) : (term307 P n) = (term287 P n).
Proof. exact (fun_ext (fun r' : nat => @lem1297295 P r' n)). Qed.
Lemma lem1297297 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1297298 (P : nadd -> Prop) (n : nat) : (term308 P n) = (term309 P n).
Proof. exact (MK_COMB (@lem1297297) (@lem1297296 P n)). Qed.
Lemma lem1297299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297300 (P : nadd -> Prop) (n : nat) : (term310 P n) = (term311 P n).
Proof. exact (MK_COMB (@lem1297299) (@lem1297298 P n)). Qed.
Lemma lem1297301 (P : nadd -> Prop) (r' : nat) (n : nat) : (term288 P n r') = (term289 P r' n).
Proof. exact (eq_refl (term288 P n r')). Qed.
Lemma lem1297302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1297303 (P : nadd -> Prop) (r' : nat) (n : nat) : (term292 P n r') = (term293 P r' n).
Proof. exact (MK_COMB (@lem1297302) (@lem1297301 P r' n)). Qed.
Lemma lem1297304 (r' : nat) (M : nat) : (Peano.le r' M) = (Peano.le r' M).
Proof. exact (eq_refl (Peano.le r' M)). Qed.
Lemma lem1297305 (P : nadd -> Prop) (n : nat) (r' : nat) (M : nat) : (term294 P n r' M) = (term295 P n r' M).
Proof. exact (MK_COMB (@lem1297303 P r' n) (@lem1297304 r' M)). Qed.
Lemma lem1297306 (P : nadd -> Prop) (n : nat) (M : nat) : (term296 P n M) = (term297 P n M).
Proof. exact (fun_ext (fun r' : nat => @lem1297305 P n r' M)). Qed.
Lemma lem1297307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297308 (P : nadd -> Prop) (n : nat) (M : nat) : (term298 P n M) = (term299 P n M).
Proof. exact (MK_COMB (@lem1297307) (@lem1297306 P n M)). Qed.
Lemma lem1297309 (P : nadd -> Prop) (n : nat) : (term312 P n) = (term313 P n).
Proof. exact (fun_ext (fun M : nat => @lem1297308 P n M)). Qed.
Lemma lem1297310 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1297311 (P : nadd -> Prop) (n : nat) : (term314 P n) = (term315 P n).
Proof. exact (MK_COMB (@lem1297310) (@lem1297309 P n)). Qed.
Lemma lem1297312 (P : nadd -> Prop) (n : nat) : (term286 P n) = (term316 P n).
Proof. exact (MK_COMB (@lem1297300 P n) (@lem1297311 P n)). Qed.
Lemma lem1297313 (P : nadd -> Prop) (n : nat) : ((term285 P n) = (term286 P n)) = ((term304 P n) = (term316 P n)).
Proof. exact (MK_COMB (@lem1297294 P n) (@lem1297312 P n)). Qed.
Lemma lem1297314 (P : nadd -> Prop) (n : nat) : (term304 P n) = (term316 P n).
Proof. exact (EQ_MP (@lem1297313 P n) (@lem1297277 P n)). Qed.
Lemma lem1297343 (P : nadd -> Prop) (n : nat) : (term316 P n) = (term304 P n).
Proof. exact (SYM (@lem1297314 P n)). Qed.
Lemma lem1297344 (x : nadd) : term317 x.
Proof. exact (@lem1279653 x). Qed.
Lemma lem1297345 (x : nadd) : (term317 x) = (term318 x).
Proof. exact (eq_refl (term317 x)). Qed.
Lemma lem1297346 (x : nadd) : term318 x.
Proof. exact (EQ_MP (@lem1297345 x) (@lem1297344 x)). Qed.
Lemma lem1297347 (x : nadd) : (term318 x) = ((term318 x) = True).
Proof. exact (@lem7 (term318 x)). Qed.
Lemma lem1297349 (P : nadd -> Prop) (a : nadd) : (P a) = ((P a) = True).
Proof. exact (@lem7 (P a)). Qed.
Lemma lem1297359 (P : nadd -> Prop) (a : nadd) (h1 : P a) : (P a) = True.
Proof. exact (EQ_MP (@lem1297349 P a) (@lem1297273 P a h1)). Qed.
Lemma lem1297360 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297361 (P : nadd -> Prop) (a : nadd) (h1 : P a) : (term319 P a) = (and True).
Proof. exact (MK_COMB (@lem1297360) (@lem1297359 P a h1)). Qed.
Lemma lem1297363 (x : nadd) : (term318 x) = True.
Proof. exact (EQ_MP (@lem1297347 x) (@lem1297346 x)). Qed.
Lemma lem1297364 (n : nat) (a : nadd) : (term320 n a) = True.
Proof. exact (@lem1297363 (term247 n a)). Qed.
Lemma lem1297365 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : (term321 P n a) = (True /\ True).
Proof. exact (MK_COMB (@lem1297361 P a h1) (@lem1297364 n a)). Qed.
Lemma lem1297367 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1297368 : (True /\ True) = True.
Proof. exact (@lem1297367 True). Qed.
Lemma lem1297369 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : (term321 P n a) = True.
Proof. exact (TRANS (@lem1297365 n P a h1) (@lem1297368)). Qed.
Lemma lem1297370 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : True = (term321 P n a).
Proof. exact (SYM (@lem1297369 n P a h1)). Qed.
Lemma lem1297371 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : term321 P n a.
Proof. exact (EQ_MP (@lem1297370 n P a h1) (@lem0)). Qed.
Lemma lem1297372 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : term322 P n.
Proof. exact (ex_intro (term323 P n) a (@lem1297371 n P a h1)). Qed.
Lemma lem1297373 (n : nat) (P : nadd -> Prop) (a : nadd) (h1 : P a) : term309 P n.
Proof. exact (ex_intro (term287 P n) (NUMERAL 0) (@lem1297372 n P a h1)). Qed.
Lemma lem1297374 (P : nadd -> Prop) (p : nat) (n : nat) (h1 : term289 P p n) : term289 P p n.
Proof. exact (h1). Qed.
Lemma lem1297375 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (h1 : term324 P p n w) : term324 P p n w.
Proof. exact (h1). Qed.
Lemma lem1297376 (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : term325 p n w.
Proof. exact (h1). Qed.
Lemma lem1297377 (P : nadd -> Prop) (w : nadd) (h1 : P w) : P w.
Proof. exact (h1). Qed.
Lemma lem1297379 (m : nat) (n : nat) : (Peano.le m n) = (term235 m n).
Proof. exact (EQ_MP (@lem1297250 m n) (@lem1297249 m n)). Qed.
Lemma lem1297380 (p : nat) (n : nat) (N : nat) : (term326 p n N) = (term327 p n N).
Proof. exact (@lem1297379 p (Nat.mul n N)). Qed.
Lemma lem1297381 (p : nat) (n : nat) (N : nat) : (term327 p n N) = (term326 p n N).
Proof. exact (SYM (@lem1297380 p n N)). Qed.
Lemma lem1297383 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1297230 x z) (@lem1297229 x z)). Qed.
Lemma lem1297384 (p : nat) (n : nat) (N : nat) : term328 p n N.
Proof. exact (@lem1297383 (nadd_of_num p) (term329 n N)). Qed.
Lemma lem1297396 (p : nat) (n : nat) (w : nadd) : (term325 p n w) = ((term325 p n w) = True).
Proof. exact (@lem7 (term325 p n w)). Qed.
Lemma lem1297401 (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : (term325 p n w) = True.
Proof. exact (EQ_MP (@lem1297396 p n w) (@lem1297376 p n w h1)). Qed.
Lemma lem1297402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297403 (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : (term330 p n w) = (and True).
Proof. exact (MK_COMB (@lem1297402) (@lem1297401 p n w h1)). Qed.
Lemma lem1297404 (w : nadd) (n : nat) (N : nat) : (term331 w n N) = (term331 w n N).
Proof. exact (eq_refl (term331 w n N)). Qed.
Lemma lem1297405 (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : (term332 p w n N) = (term333 w n N).
Proof. exact (MK_COMB (@lem1297403 p n w h1) (@lem1297404 w n N)). Qed.
Lemma lem1297407 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1297408 (w : nadd) (n : nat) (N : nat) : (term333 w n N) = (term331 w n N).
Proof. exact (@lem1297407 (term331 w n N)). Qed.
Lemma lem1297409 (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : (term332 p w n N) = (term331 w n N).
Proof. exact (TRANS (@lem1297405 N p n w h1) (@lem1297408 w n N)). Qed.
Lemma lem1297410 (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term325 p n w) : (term331 w n N) = (term332 p w n N).
Proof. exact (SYM (@lem1297409 N p n w h1)). Qed.
Lemma lem1297412 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1297202 x z) (@lem1297201 x z)). Qed.
Lemma lem1297413 (w : nadd) (n : nat) (N : nat) : term334 w n N.
Proof. exact (@lem1297412 (term247 n w) (term329 n N)). Qed.
Lemma lem1297415 (y : nadd) (x : nadd) (z : nadd) : term6 y x z.
Proof. exact (EQ_MP (@lem1297174 y x z) (@lem1297173 y x z)). Qed.
Lemma lem1297416 (w : nadd) (n : nat) (N : nat) : term335 w n N.
Proof. exact (@lem1297415 w (nadd_of_num n) (nadd_of_num N)). Qed.
Lemma lem1297418 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1297144 x z) (@lem1297143 x z)). Qed.
Lemma lem1297419 (w : nadd) (N : nat) : term336 w N.
Proof. exact (@lem1297418 w (nadd_of_num N)). Qed.
Lemma lem1297427 (m : nadd) (N : nat) : (term272 m N) = ((term272 m N) = True).
Proof. exact (@lem7 (term272 m N)). Qed.
Lemma lem1297436 (m : nadd) (N : nat) (h1 : term272 m N) : (term272 m N) = True.
Proof. exact (EQ_MP (@lem1297427 m N) (@lem1297255 m N h1)). Qed.
Lemma lem1297437 (w : nadd) (m : nadd) : (term337 w m) = (term337 w m).
Proof. exact (eq_refl (term337 w m)). Qed.
Lemma lem1297438 (w : nadd) (m : nadd) (N : nat) (h1 : term272 m N) : (term338 w m N) = (term339 w m).
Proof. exact (MK_COMB (@lem1297437 w m) (@lem1297436 m N h1)). Qed.
Lemma lem1297440 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1297441 (w : nadd) (m : nadd) : (term339 w m) = (nadd_le w m).
Proof. exact (@lem1297440 (nadd_le w m)). Qed.
Lemma lem1297442 (w : nadd) (m : nadd) (N : nat) (h1 : term272 m N) : (term338 w m N) = (nadd_le w m).
Proof. exact (TRANS (@lem1297438 w m N h1) (@lem1297441 w m)). Qed.
Lemma lem1297443 (w : nadd) (m : nadd) (N : nat) (h1 : term272 m N) : (nadd_le w m) = (term338 w m N).
Proof. exact (SYM (@lem1297442 w m N h1)). Qed.
Lemma lem1297444 (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term282 P m.
Proof. exact (h1). Qed.
Lemma lem1297445 (x : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term340 P m x.
Proof. exact (@lem1297444 P m h1 x). Qed.
Lemma lem1297446 (P : nadd -> Prop) (x : nadd) (m : nadd) : (term340 P m x) = (term341 P x m).
Proof. exact (eq_refl (term340 P m x)). Qed.
Lemma lem1297447 (x : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term341 P x m.
Proof. exact (EQ_MP (@lem1297446 P x m) (@lem1297445 x P m h1)). Qed.
Lemma lem1297448 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1297449 (m : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P m) (h2 : P x) : nadd_le x m.
Proof. exact (@lem1297447 x P m h1 (@lem1297448 P x h2)). Qed.
Lemma lem1297450 (m : nadd) (P : nadd -> Prop) (x : nadd) (h1 : P x) : term342 P x m.
Proof. exact (fun h0 : term282 P m => @lem1297449 m P x h0 h1). Qed.
Lemma lem1297451 (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term282 P m.
Proof. exact (h1). Qed.
Lemma lem1297452 (m : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P m) (h2 : P x) : nadd_le x m.
Proof. exact (@lem1297450 m P x h2 (@lem1297451 P m h1)). Qed.
Lemma lem1297453 (x : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term341 P x m.
Proof. exact (fun h0 : P x => @lem1297452 m P x h1 h0). Qed.
Lemma lem1297454 (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term282 P m.
Proof. exact (fun x : nadd => @lem1297453 x P m h1). Qed.
Lemma lem1297455 (P : nadd -> Prop) (m : nadd) : term343 P m.
Proof. exact (fun h0 : term282 P m => @lem1297454 P m h0). Qed.
Lemma lem1297456 (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term282 P m.
Proof. exact (@lem1297455 P m (@lem1297271 P m h1)). Qed.
Lemma lem1297457 (x : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term340 P m x.
Proof. exact (@lem1297456 P m h1 x). Qed.
Lemma lem1297458 (P : nadd -> Prop) (x : nadd) (m : nadd) : (term340 P m x) = (term341 P x m).
Proof. exact (eq_refl (term340 P m x)). Qed.
Lemma lem1297461 (x : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term341 P x m.
Proof. exact (EQ_MP (@lem1297458 P x m) (@lem1297457 x P m h1)). Qed.
Lemma lem1297462 (w : nadd) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term341 P w m.
Proof. exact (@lem1297461 w P m h1). Qed.
Lemma lem1297472 (P : nadd -> Prop) (w : nadd) : (P w) = ((P w) = True).
Proof. exact (@lem7 (P w)). Qed.
Lemma lem1297477 (P : nadd -> Prop) (w : nadd) (h1 : P w) : (P w) = True.
Proof. exact (EQ_MP (@lem1297472 P w) (@lem1297377 P w h1)). Qed.
Lemma lem1297478 (P : nadd -> Prop) (w : nadd) (h1 : P w) : True = (P w).
Proof. exact (SYM (@lem1297477 P w h1)). Qed.
Lemma lem1297479 (P : nadd -> Prop) (w : nadd) (h1 : P w) : P w.
Proof. exact (EQ_MP (@lem1297478 P w h1) (@lem0)). Qed.
Lemma lem1297480 (m : nadd) (P : nadd -> Prop) (w : nadd) (h1 : term282 P m) (h2 : P w) : nadd_le w m.
Proof. exact (@lem1297462 w P m h1 (@lem1297479 P w h2)). Qed.
Lemma lem1297481 (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term338 w m N.
Proof. exact (EQ_MP (@lem1297443 w m N h3) (@lem1297480 m P w h1 h2)). Qed.
Lemma lem1297482 (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term344 w N.
Proof. exact (ex_intro (term345 w N) m (@lem1297481 P w m N h1 h2 h3)). Qed.
Lemma lem1297483 (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term272 w N.
Proof. exact (@lem1297419 w N (@lem1297482 P w m N h1 h2 h3)). Qed.
Lemma lem1297484 (n : nat) (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term346 w n N.
Proof. exact (@lem1297416 w n N (@lem1297483 P w m N h1 h2 h3)). Qed.
Lemma lem1297486 (x : nadd) (y : nadd) : term154 x y.
Proof. exact (EQ_MP (@lem1297116 x y) (@lem1297115 x y)). Qed.
Lemma lem1297487 (n : nat) (N : nat) : term347 n N.
Proof. exact (@lem1297486 (term348 n N) (term329 n N)). Qed.
Lemma lem1297488 (m : nat) : term146 m.
Proof. exact (@lem1279539 m). Qed.
Lemma lem1297489 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem1297490 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem1297489 m) (@lem1297488 m)). Qed.
Lemma lem1297491 (m : nat) (n : nat) : term148 m n.
Proof. exact (@lem1297490 m n). Qed.
Lemma lem1297492 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem1297495 (m : nat) (n : nat) : term149 m n.
Proof. exact (EQ_MP (@lem1297492 m n) (@lem1297491 m n)). Qed.
Lemma lem1297496 (n : nat) (N : nat) : term149 n N.
Proof. exact (@lem1297495 n N). Qed.
Lemma lem1297497 (n : nat) (N : nat) : term349 n N.
Proof. exact (@lem1297487 n N (@lem1297496 n N)). Qed.
Lemma lem1297498 (n : nat) (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term350 w n N.
Proof. exact (conj (@lem1297484 n P w m N h1 h2 h3) (@lem1297497 n N)). Qed.
Lemma lem1297499 (n : nat) (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term351 w n N.
Proof. exact (ex_intro (term352 w n N) (term348 n N) (@lem1297498 n P w m N h1 h2 h3)). Qed.
Lemma lem1297500 (n : nat) (P : nadd -> Prop) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) : term331 w n N.
Proof. exact (@lem1297413 w n N (@lem1297499 n P w m N h1 h2 h3)). Qed.
Lemma lem1297501 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term332 p w n N.
Proof. exact (EQ_MP (@lem1297410 N p n w h4) (@lem1297500 n P w m N h1 h2 h3)). Qed.
Lemma lem1297502 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term353 p n N.
Proof. exact (ex_intro (term354 p n N) (term247 n w) (@lem1297501 P m N p n w h1 h2 h3 h4)). Qed.
Lemma lem1297503 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term327 p n N.
Proof. exact (@lem1297384 p n N (@lem1297502 P m N p n w h1 h2 h3 h4)). Qed.
Lemma lem1297504 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term326 p n N.
Proof. exact (EQ_MP (@lem1297381 p n N) (@lem1297503 P m N p n w h1 h2 h3 h4)). Qed.
Lemma lem1297505 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (h1 : term324 P p n w) : term325 p n w.
Proof. exact (proj2 (@lem1297375 P p n w h1)). Qed.
Lemma lem1297506 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (h1 : term324 P p n w) : P w.
Proof. exact (proj1 (@lem1297375 P p n w h1)). Qed.
Lemma lem1297507 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : (term325 p n w) = (term326 p n N).
Proof. exact (prop_ext (fun h5 : term325 p n w => @lem1297504 P m N p n w h1 h2 h3 h4) (fun h5 : term326 p n N => @lem1297376 p n w h4)). Qed.
Lemma lem1297508 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term326 p n N.
Proof. exact (EQ_MP (@lem1297507 P m N p n w h1 h2 h3 h4) (@lem1297376 p n w h4)). Qed.
Lemma lem1297509 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : (P w) = (term326 p n N).
Proof. exact (prop_ext (fun h5 : P w => @lem1297508 P m N p n w h1 h2 h3 h4) (fun h5 : term326 p n N => @lem1297377 P w h2)). Qed.
Lemma lem1297510 (P : nadd -> Prop) (m : nadd) (N : nat) (p : nat) (n : nat) (w : nadd) (h1 : term282 P m) (h2 : P w) (h3 : term272 m N) (h4 : term325 p n w) : term326 p n N.
Proof. exact (EQ_MP (@lem1297509 P m N p n w h1 h2 h3 h4) (@lem1297377 P w h2)). Qed.
Lemma lem1297511 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term324 P p n w) (h4 : term272 m N) : (term325 p n w) = (term326 p n N).
Proof. exact (prop_ext (fun h5 : term325 p n w => @lem1297510 P m N p n w h1 h2 h4 h5) (fun h5 : term326 p n N => @lem1297505 P p n w h3)). Qed.
Lemma lem1297512 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : P w) (h3 : term324 P p n w) (h4 : term272 m N) : term326 p n N.
Proof. exact (EQ_MP (@lem1297511 P p n w m N h1 h2 h3 h4) (@lem1297505 P p n w h3)). Qed.
Lemma lem1297513 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term324 P p n w) (h3 : term272 m N) : (P w) = (term326 p n N).
Proof. exact (prop_ext (fun h4 : P w => @lem1297512 P p n w m N h1 h4 h2 h3) (fun h4 : term326 p n N => @lem1297506 P p n w h2)). Qed.
Lemma lem1297514 (P : nadd -> Prop) (p : nat) (n : nat) (w : nadd) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term324 P p n w) (h3 : term272 m N) : term326 p n N.
Proof. exact (EQ_MP (@lem1297513 P p n w m N h1 h2 h3) (@lem1297506 P p n w h2)). Qed.
Lemma lem1297515 (P : nadd -> Prop) (p : nat) (n : nat) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term289 P p n) (h3 : term272 m N) : term326 p n N.
Proof. exact (ex_elim (@lem1297374 P p n h2) (fun w : nadd => fun h0 : term355 P p n w => @lem1297514 P p n w m N h1 h0 h3)). Qed.
Lemma lem1297516 (p : nat) (n : nat) (P : nadd -> Prop) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term272 m N) : term356 P p n N.
Proof. exact (fun h0 : term289 P p n => @lem1297515 P p n m N h1 h0 h2). Qed.
Lemma lem1297521 (n : nat) (P : nadd -> Prop) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term272 m N) : term357 P n N.
Proof. exact (fun p : nat => @lem1297516 p n P m N h1 h2). Qed.
Lemma lem1297522 (n : nat) (P : nadd -> Prop) (m : nadd) (N : nat) (h1 : term282 P m) (h2 : term272 m N) : term315 P n.
Proof. exact (ex_intro (term313 P n) (Nat.mul n N) (@lem1297521 n P m N h1 h2)). Qed.
Lemma lem1297523 (n : nat) (P : nadd -> Prop) (m : nadd) (h1 : term282 P m) : term315 P n.
Proof. exact (ex_elim (@lem1297254 m) (fun N : nat => fun h0 : term358 m N => @lem1297522 n P m N h1 h0)). Qed.
Lemma lem1297524 (n : nat) (m : nadd) (P : nadd -> Prop) (a : nadd) (h1 : term282 P m) (h2 : P a) : term316 P n.
Proof. exact (conj (@lem1297373 n P a h2) (@lem1297523 n P m h1)). Qed.
Lemma lem1297525 (n : nat) (m : nadd) (P : nadd -> Prop) (a : nadd) (h1 : term282 P m) (h2 : P a) : term304 P n.
Proof. exact (EQ_MP (@lem1297343 P n) (@lem1297524 n m P a h1 h2)). Qed.
Lemma lem1297530 (m : nadd) (P : nadd -> Prop) (a : nadd) (h1 : term282 P m) (h2 : P a) : term284 P.
Proof. exact (fun n : nat => @lem1297525 n m P a h1 h2). Qed.
Lemma lem1297534 {A B : Type'} (P : type1413 A B) : (term268 A B P) = (term269 A B P).
Proof. exact (EQ_MP (@lem1297093 A B P) (@lem1297092 A B P)). Qed.
Lemma lem1297535 (P : type1605) : (term359 P) = (term360 P).
Proof. exact (@lem1297534 nat nat P). Qed.
Lemma lem1297536 (P : nadd -> Prop) : (term361 P) = (term362 P).
Proof. exact (@lem1297535 (term363 P)). Qed.
Lemma lem1297537 (P : nadd -> Prop) (n : nat) : (term364 P n) = (term303 P n).
Proof. exact (eq_refl (term364 P n)). Qed.
Lemma lem1297538 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1297539 (P : nadd -> Prop) (n : nat) (r : nat) : (term365 P n r) = (term366 P n r).
Proof. exact (MK_COMB (@lem1297537 P n) (@lem1297538 r)). Qed.
Lemma lem1297540 (P : nadd -> Prop) (n : nat) (r : nat) : (term366 P n r) = (term301 P n r).
Proof. exact (eq_refl (term366 P n r)). Qed.
Lemma lem1297541 (P : nadd -> Prop) (n : nat) (r : nat) : (term365 P n r) = (term301 P n r).
Proof. exact (TRANS (@lem1297539 P n r) (@lem1297540 P n r)). Qed.
Lemma lem1297542 (P : nadd -> Prop) (n : nat) : (term367 P n) = (term303 P n).
Proof. exact (fun_ext (fun r : nat => @lem1297541 P n r)). Qed.
Lemma lem1297543 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1297544 (P : nadd -> Prop) (n : nat) : (term368 P n) = (term304 P n).
Proof. exact (MK_COMB (@lem1297543) (@lem1297542 P n)). Qed.
Lemma lem1297545 (P : nadd -> Prop) : (term369 P) = (term370 P).
Proof. exact (fun_ext (fun n : nat => @lem1297544 P n)). Qed.
Lemma lem1297546 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297547 (P : nadd -> Prop) : (term361 P) = (term284 P).
Proof. exact (MK_COMB (@lem1297546) (@lem1297545 P)). Qed.
Lemma lem1297548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1297549 (P : nadd -> Prop) : (term371 P) = (term372 P).
Proof. exact (MK_COMB (@lem1297548) (@lem1297547 P)). Qed.
Lemma lem1297550 (P : nadd -> Prop) (n : nat) : (term364 P n) = (term303 P n).
Proof. exact (eq_refl (term364 P n)). Qed.
Lemma lem1297551 (r : nat -> nat) (n : nat) : (r n) = (r n).
Proof. exact (eq_refl (r n)). Qed.
Lemma lem1297552 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term373 P r n) = (term374 P r n).
Proof. exact (MK_COMB (@lem1297550 P n) (@lem1297551 r n)). Qed.
Lemma lem1297553 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term374 P r n) = (term375 P r n).
Proof. exact (eq_refl (term374 P r n)). Qed.
Lemma lem1297554 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term373 P r n) = (term375 P r n).
Proof. exact (TRANS (@lem1297552 P r n) (@lem1297553 P r n)). Qed.
Lemma lem1297555 (P : nadd -> Prop) (r : nat -> nat) : (term376 P r) = (term377 P r).
Proof. exact (fun_ext (fun n : nat => @lem1297554 P r n)). Qed.
Lemma lem1297556 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297557 (P : nadd -> Prop) (r : nat -> nat) : (term378 P r) = (term379 P r).
Proof. exact (MK_COMB (@lem1297556) (@lem1297555 P r)). Qed.
Lemma lem1297558 (P : nadd -> Prop) : (term380 P) = (term381 P).
Proof. exact (fun_ext (fun r : nat -> nat => @lem1297557 P r)). Qed.
Lemma lem1297559 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1297560 (P : nadd -> Prop) : (term362 P) = (term382 P).
Proof. exact (MK_COMB (@lem1297559) (@lem1297558 P)). Qed.
Lemma lem1297561 (P : nadd -> Prop) : ((term361 P) = (term362 P)) = ((term284 P) = (term382 P)).
Proof. exact (MK_COMB (@lem1297549 P) (@lem1297560 P)). Qed.
Lemma lem1297562 (P : nadd -> Prop) : (term284 P) = (term382 P).
Proof. exact (EQ_MP (@lem1297561 P) (@lem1297536 P)). Qed.
Lemma lem1297563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1297564 (P : nadd -> Prop) : (term383 P) = (term384 P).
Proof. exact (MK_COMB (@lem1297563) (@lem1297562 P)). Qed.
Lemma lem1297589 (P : nadd -> Prop) : (term385 P) = (term385 P).
Proof. exact (eq_refl (term385 P)). Qed.
Lemma lem1297590 (P : nadd -> Prop) : (term386 P) = (term387 P).
Proof. exact (MK_COMB (@lem1297564 P) (@lem1297589 P)). Qed.
Lemma lem1297591 (P : nadd -> Prop) : (term387 P) = (term386 P).
Proof. exact (SYM (@lem1297590 P)). Qed.
Lemma lem1297592 (P : nadd -> Prop) (h1 : term382 P) : term382 P.
Proof. exact (h1). Qed.
Lemma lem1297593 (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term379 P r.
Proof. exact (h1). Qed.
Lemma lem1297594 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term388 P r n.
Proof. exact (@lem1297593 P r h1 n). Qed.
Lemma lem1297595 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term388 P r n) = (term375 P r n).
Proof. exact (eq_refl (term388 P r n)). Qed.
Lemma lem1297596 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term375 P r n.
Proof. exact (EQ_MP (@lem1297595 P r n) (@lem1297594 n P r h1)). Qed.
Lemma lem1297597 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term389 P r n.
Proof. exact (proj2 (@lem1297596 n P r h1)). Qed.
Lemma lem1297598 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term390 P r n.
Proof. exact (proj1 (@lem1297596 n P r h1)). Qed.
Lemma lem1297599 (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term391 P r.
Proof. exact (fun n : nat => @lem1297598 n P r h1). Qed.
Lemma lem1297600 (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term392 P r.
Proof. exact (fun n : nat => @lem1297597 n P r h1). Qed.
Lemma lem1297601 (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term392 P r.
Proof. exact (h1). Qed.
Lemma lem1297602 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term393 P r n.
Proof. exact (@lem1297601 P r h1 n). Qed.
Lemma lem1297603 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term393 P r n) = (term389 P r n).
Proof. exact (eq_refl (term393 P r n)). Qed.
Lemma lem1297604 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term389 P r n.
Proof. exact (EQ_MP (@lem1297603 P r n) (@lem1297602 n P r h1)). Qed.
Lemma lem1297605 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term394 P r n.
Proof. exact (@lem1297604 n P r h1 (term395 r n)). Qed.
Lemma lem1297606 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term394 P r n) = (term396 P r n).
Proof. exact (eq_refl (term394 P r n)). Qed.
Lemma lem1297607 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term396 P r n.
Proof. exact (EQ_MP (@lem1297606 P r n) (@lem1297605 n P r h1)). Qed.
Lemma lem1297608 (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term397 P r.
Proof. exact (fun n : nat => @lem1297607 n P r h1). Qed.
Lemma lem1297624 (m : nat) (n : nat) : (term266 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1297090 m n) (@lem1297089 m n)). Qed.
Lemma lem1297625 (r : nat -> nat) (n : nat) : (term398 r n) = (term399 r n).
Proof. exact (@lem1297624 (r n) (r n)). Qed.
Lemma lem1297627 (n : nat) : (Peano.lt n n) = False.
Proof. exact (@lem1297084 n (@lem1297083 n)). Qed.
Lemma lem1297628 (r : nat -> nat) (n : nat) : (term399 r n) = False.
Proof. exact (@lem1297627 (r n)). Qed.
Lemma lem1297629 (r : nat -> nat) (n : nat) : (term398 r n) = False.
Proof. exact (TRANS (@lem1297625 r n) (@lem1297628 r n)). Qed.
Lemma lem1297630 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term400 P r n) = (term400 P r n).
Proof. exact (eq_refl (term400 P r n)). Qed.
Lemma lem1297631 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term396 P r n) = (term401 P r n).
Proof. exact (MK_COMB (@lem1297630 P r n) (@lem1297629 r n)). Qed.
Lemma lem1297633 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1297634 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term401 P r n) = (term402 P r n).
Proof. exact (@lem1297633 (term403 P r n)). Qed.
Lemma lem1297636 {A : Type'} (P : A -> Prop) : (term258 A P) = (term259 A P).
Proof. exact (EQ_MP (@lem1297079 A P) (@lem1297078 A P)). Qed.
Lemma lem1297637 (P : nadd -> Prop) : (term404 P) = (term405 P).
Proof. exact (@lem1297636 nadd P). Qed.
Lemma lem1297638 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term406 P r n) = (term407 P r n).
Proof. exact (@lem1297637 (term408 P r n)). Qed.
Lemma lem1297639 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) : (term409 P r n x) = (term410 P r n x).
Proof. exact (eq_refl (term409 P r n x)). Qed.
Lemma lem1297640 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term411 P r n) = (term408 P r n).
Proof. exact (fun_ext (fun x : nadd => @lem1297639 P r n x)). Qed.
Lemma lem1297641 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1297642 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term412 P r n) = (term403 P r n).
Proof. exact (MK_COMB (@lem1297641) (@lem1297640 P r n)). Qed.
Lemma lem1297643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1297644 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term406 P r n) = (term402 P r n).
Proof. exact (MK_COMB (@lem1297643) (@lem1297642 P r n)). Qed.
Lemma lem1297645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1297646 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term413 P r n) = (term414 P r n).
Proof. exact (MK_COMB (@lem1297645) (@lem1297644 P r n)). Qed.
Lemma lem1297647 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) : (term409 P r n x) = (term410 P r n x).
Proof. exact (eq_refl (term409 P r n x)). Qed.
Lemma lem1297648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1297649 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) : (term415 P r n x) = (term416 P r n x).
Proof. exact (MK_COMB (@lem1297648) (@lem1297647 P r n x)). Qed.
Lemma lem1297650 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term417 P r n) = (term418 P r n).
Proof. exact (fun_ext (fun x : nadd => @lem1297649 P r n x)). Qed.
Lemma lem1297651 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1297652 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term407 P r n) = (term419 P r n).
Proof. exact (MK_COMB (@lem1297651) (@lem1297650 P r n)). Qed.
Lemma lem1297653 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : ((term406 P r n) = (term407 P r n)) = ((term402 P r n) = (term419 P r n)).
Proof. exact (MK_COMB (@lem1297646 P r n) (@lem1297652 P r n)). Qed.
Lemma lem1297654 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term402 P r n) = (term419 P r n).
Proof. exact (EQ_MP (@lem1297653 P r n) (@lem1297638 P r n)). Qed.
Lemma lem1297661 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term401 P r n) = (term419 P r n).
Proof. exact (TRANS (@lem1297634 P r n) (@lem1297654 P r n)). Qed.
Lemma lem1297662 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term396 P r n) = (term419 P r n).
Proof. exact (TRANS (@lem1297631 P r n) (@lem1297661 P r n)). Qed.
Lemma lem1297663 (P : nadd -> Prop) (r : nat -> nat) : (term420 P r) = (term421 P r).
Proof. exact (fun_ext (fun n : nat => @lem1297662 P r n)). Qed.
Lemma lem1297664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1297665 (P : nadd -> Prop) (r : nat -> nat) : (term397 P r) = (term422 P r).
Proof. exact (MK_COMB (@lem1297664) (@lem1297663 P r)). Qed.
Lemma lem1297670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1297671 (P : nadd -> Prop) (r : nat -> nat) : (term423 P r) = (term424 P r).
Proof. exact (MK_COMB (@lem1297670) (@lem1297665 P r)). Qed.
Lemma lem1297708 (r : nat -> nat) (P : nadd -> Prop) : (term425 r P) = (term425 r P).
Proof. exact (eq_refl (term425 r P)). Qed.
Lemma lem1297709 (r : nat -> nat) (P : nadd -> Prop) : (term426 r P) = (term427 r P).
Proof. exact (MK_COMB (@lem1297671 P r) (@lem1297708 r P)). Qed.
Lemma lem1297712 (r : nat -> nat) (P : nadd -> Prop) : (term427 r P) = (term426 r P).
Proof. exact (SYM (@lem1297709 r P)). Qed.
Lemma lem1297713 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term422 P r.
Proof. exact (h1). Qed.
Lemma lem1297714 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term428 P r n.
Proof. exact (@lem1297713 P r h1 n). Qed.
Lemma lem1297715 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term428 P r n) = (term419 P r n).
Proof. exact (eq_refl (term428 P r n)). Qed.
Lemma lem1297716 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term419 P r n.
Proof. exact (EQ_MP (@lem1297715 P r n) (@lem1297714 n P r h1)). Qed.
Lemma lem1297717 (n : nat) (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term429 P r n x.
Proof. exact (@lem1297716 n P r h1 x). Qed.
Lemma lem1297718 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) : (term429 P r n x) = (term416 P r n x).
Proof. exact (eq_refl (term429 P r n x)). Qed.
Lemma lem1297719 (n : nat) (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term416 P r n x.
Proof. exact (EQ_MP (@lem1297718 P r n x) (@lem1297717 n x P r h1)). Qed.
Lemma lem1297720 (n : nat) (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term430 P r n x.
Proof. exact (conj (@lem1297038 r n x) (@lem1297719 n x P r h1)). Qed.
Lemma lem1297722 (b : Prop) (c : Prop) (a : Prop) : term431 b c a.
Proof. exact (fun h0 : term252 a c b => @lem1297076 a c b h0). Qed.
Lemma lem1297723 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (n : nat) : term432 P x r n.
Proof. exact (@lem1297722 (term433 r n x) (P x) (term434 x r n)). Qed.
Lemma lem1297724 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term435 P x r n.
Proof. exact (@lem1297723 P x r n (@lem1297720 n x P r h1)). Qed.
Lemma lem1297725 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term436 P r n.
Proof. exact (fun x : nadd => @lem1297724 x n P r h1). Qed.
Lemma lem1297726 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term437 P r.
Proof. exact (fun n : nat => @lem1297725 n P r h1). Qed.
Lemma lem1297727 (P : nadd -> Prop) (r : nat -> nat) (h1 : term391 P r) : term391 P r.
Proof. exact (h1). Qed.
Lemma lem1297728 (r : nat -> nat) (h1 : term438 r) : term438 r.
Proof. exact (h1). Qed.
Lemma lem1297729 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term391 P r) : term439 P r n.
Proof. exact (@lem1297727 P r h1 n). Qed.
Lemma lem1297730 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term439 P r n) = (term390 P r n).
Proof. exact (eq_refl (term439 P r n)). Qed.
Lemma lem1297731 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term391 P r) : term390 P r n.
Proof. exact (EQ_MP (@lem1297730 P r n) (@lem1297729 n P r h1)). Qed.
Lemma lem1297732 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : term440 P r n x.
Proof. exact (h1). Qed.
Lemma lem1297733 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term441 r n x.
Proof. exact (h1). Qed.
Lemma lem1297734 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1297736 (m : nat) (n : nat) : (Peano.le m n) = (term235 m n).
Proof. exact (EQ_MP (@lem1297031 m n) (@lem1297030 m n)). Qed.
Lemma lem1297737 (r : nat -> nat) (i : nat) (n : nat) : (term442 r i n) = (term443 r i n).
Proof. exact (@lem1297736 (term444 i r n) (term445 r i n)). Qed.
Lemma lem1297738 (r : nat -> nat) (i : nat) (n : nat) : (term443 r i n) = (term442 r i n).
Proof. exact (SYM (@lem1297737 r i n)). Qed.
Lemma lem1297740 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1297011 x z) (@lem1297010 x z)). Qed.
Lemma lem1297741 (r : nat -> nat) (i : nat) (n : nat) : term446 r i n.
Proof. exact (@lem1297740 (term447 i r n) (term448 r i n)). Qed.
Lemma lem1297743 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296983 x z) (@lem1296982 x z)). Qed.
Lemma lem1297744 (r : nat -> nat) (i : nat) (n : nat) (x : nadd) : term449 r i n x.
Proof. exact (@lem1297743 (term447 i r n) (term450 i n x)). Qed.
Lemma lem1297746 (x : nadd) (y : nadd) : term154 x y.
Proof. exact (EQ_MP (@lem1296955 x y) (@lem1296954 x y)). Qed.
Lemma lem1297747 (i : nat) (r : nat -> nat) (n : nat) : term451 i r n.
Proof. exact (@lem1297746 (term447 i r n) (term452 i r n)). Qed.
Lemma lem1297749 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1296932 y x) (@lem1296931 x y)). Qed.
Lemma lem1297750 (i : nat) (r : nat -> nat) (n : nat) : (term453 i r n) = (term454 i r n).
Proof. exact (@lem1297749 (term452 i r n) (term447 i r n)). Qed.
Lemma lem1297751 (i : nat) (r : nat -> nat) (n : nat) : (term454 i r n) = (term453 i r n).
Proof. exact (SYM (@lem1297750 i r n)). Qed.
Lemma lem1297752 (m : nat) : term146 m.
Proof. exact (@lem1279539 m). Qed.
Lemma lem1297753 (m : nat) : (term146 m) = (term147 m).
Proof. exact (eq_refl (term146 m)). Qed.
Lemma lem1297754 (m : nat) : term147 m.
Proof. exact (EQ_MP (@lem1297753 m) (@lem1297752 m)). Qed.
Lemma lem1297755 (m : nat) (n : nat) : term148 m n.
Proof. exact (@lem1297754 m n). Qed.
Lemma lem1297756 (m : nat) (n : nat) : (term148 m n) = (term149 m n).
Proof. exact (eq_refl (term148 m n)). Qed.
Lemma lem1297759 (m : nat) (n : nat) : term149 m n.
Proof. exact (EQ_MP (@lem1297756 m n) (@lem1297755 m n)). Qed.
Lemma lem1297760 (i : nat) (r : nat -> nat) (n : nat) : term454 i r n.
Proof. exact (@lem1297759 i (r n)). Qed.
Lemma lem1297761 (i : nat) (r : nat -> nat) (n : nat) : term453 i r n.
Proof. exact (EQ_MP (@lem1297751 i r n) (@lem1297760 i r n)). Qed.
Lemma lem1297762 (i : nat) (r : nat -> nat) (n : nat) : term455 i r n.
Proof. exact (@lem1297747 i r n (@lem1297761 i r n)). Qed.
Lemma lem1297764 (y : nadd) (x : nadd) (z : nadd) : term6 y x z.
Proof. exact (EQ_MP (@lem1296926 y x z) (@lem1296925 y x z)). Qed.
Lemma lem1297765 (r : nat -> nat) (i : nat) (n : nat) (x : nadd) : term456 r i n x.
Proof. exact (@lem1297764 (term457 r n) (nadd_of_num i) (term247 n x)). Qed.
Lemma lem1297788 (r : nat -> nat) (n : nat) (x : nadd) : (term441 r n x) = ((term441 r n x) = True).
Proof. exact (@lem7 (term441 r n x)). Qed.
Lemma lem1297791 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term441 r n x) = True.
Proof. exact (EQ_MP (@lem1297788 r n x) (@lem1297733 r n x h1)). Qed.
Lemma lem1297792 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : True = (term441 r n x).
Proof. exact (SYM (@lem1297791 r n x h1)). Qed.
Lemma lem1297793 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term441 r n x.
Proof. exact (EQ_MP (@lem1297792 r n x h1) (@lem0)). Qed.
Lemma lem1297794 (i : nat) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term458 r i n x.
Proof. exact (@lem1297765 r i n x (@lem1297793 r n x h1)). Qed.
Lemma lem1297795 (i : nat) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term459 r i n x.
Proof. exact (conj (@lem1297762 i r n) (@lem1297794 i r n x h1)). Qed.
Lemma lem1297796 (i : nat) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term460 r i n x.
Proof. exact (ex_intro (term461 r i n x) (term452 i r n) (@lem1297795 i r n x h1)). Qed.
Lemma lem1297797 (i : nat) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term462 r i n x.
Proof. exact (@lem1297744 r i n x (@lem1297796 i r n x h1)). Qed.
Lemma lem1297799 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296896 x z) (@lem1296895 x z)). Qed.
Lemma lem1297800 (x : nadd) (r : nat -> nat) (i : nat) (n : nat) : term463 x r i n.
Proof. exact (@lem1297799 (term450 i n x) (term448 r i n)). Qed.
Lemma lem1297802 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296868 x z) (@lem1296867 x z)). Qed.
Lemma lem1297803 (x : nadd) (n : nat) (r : nat -> nat) (i : nat) : term464 x n r i.
Proof. exact (@lem1297802 (term450 i n x) (term465 n r i)). Qed.
Lemma lem1297805 (x : nadd) (y : nadd) : term154 x y.
Proof. exact (EQ_MP (@lem1296840 x y) (@lem1296839 x y)). Qed.
Lemma lem1297806 (n : nat) (i : nat) (x : nadd) : term466 n i x.
Proof. exact (@lem1297805 (term450 i n x) (term450 n i x)). Qed.
Lemma lem1297808 (x : nadd) (z : nadd) : term226 x z.
Proof. exact (EQ_MP (@lem1296817 x z) (@lem1296816 x z)). Qed.
Lemma lem1297809 (n : nat) (i : nat) (x : nadd) : term467 n i x.
Proof. exact (@lem1297808 (term450 i n x) (term450 n i x)). Qed.
Lemma lem1297813 (x : nadd) (y : nadd) (z : nadd) : (term196 x y z) = True.
Proof. exact (EQ_MP (@lem1296789 x y z) (@lem1296788 x y z)). Qed.
Lemma lem1297814 (i : nat) (n : nat) (x : nadd) : (term468 i n x) = True.
Proof. exact (@lem1297813 (nadd_of_num i) (nadd_of_num n) x). Qed.
Lemma lem1297815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297816 (i : nat) (n : nat) (x : nadd) : (term469 i n x) = (and True).
Proof. exact (MK_COMB (@lem1297815) (@lem1297814 i n x)). Qed.
Lemma lem1297817 (n : nat) (i : nat) (x : nadd) : (term470 n i x) = (term470 n i x).
Proof. exact (eq_refl (term470 n i x)). Qed.
Lemma lem1297818 (n : nat) (i : nat) (x : nadd) : (term471 n i x) = (term472 n i x).
Proof. exact (MK_COMB (@lem1297816 i n x) (@lem1297817 n i x)). Qed.
Lemma lem1297820 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1297821 (n : nat) (i : nat) (x : nadd) : (term472 n i x) = (term470 n i x).
Proof. exact (@lem1297820 (term470 n i x)). Qed.
Lemma lem1297822 (n : nat) (i : nat) (x : nadd) : (term471 n i x) = (term470 n i x).
Proof. exact (TRANS (@lem1297818 n i x) (@lem1297821 n i x)). Qed.
Lemma lem1297823 (n : nat) (i : nat) (x : nadd) : (term470 n i x) = (term471 n i x).
Proof. exact (SYM (@lem1297822 n i x)). Qed.
Lemma lem1297825 (x : nadd) (z : nadd) : term226 x z.
Proof. exact (EQ_MP (@lem1296778 x z) (@lem1296777 x z)). Qed.
Lemma lem1297826 (n : nat) (i : nat) (x : nadd) : term473 n i x.
Proof. exact (@lem1297825 (term474 i n x) (term450 n i x)). Qed.
Lemma lem1297830 (x : nadd) (y : nadd) (z : nadd) : (term197 x y z) = True.
Proof. exact (EQ_MP (@lem1296750 x y z) (@lem1296749 x y z)). Qed.
Lemma lem1297831 (n : nat) (i : nat) (x : nadd) : (term475 n i x) = True.
Proof. exact (@lem1297830 (nadd_of_num n) (nadd_of_num i) x). Qed.
Lemma lem1297832 (n : nat) (i : nat) (x : nadd) : (term476 n i x) = (term476 n i x).
Proof. exact (eq_refl (term476 n i x)). Qed.
Lemma lem1297833 (n : nat) (i : nat) (x : nadd) : (term477 n i x) = (term478 n i x).
Proof. exact (MK_COMB (@lem1297832 n i x) (@lem1297831 n i x)). Qed.
Lemma lem1297835 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1297836 (n : nat) (i : nat) (x : nadd) : (term478 n i x) = (term479 n i x).
Proof. exact (@lem1297835 (term479 n i x)). Qed.
Lemma lem1297837 (n : nat) (i : nat) (x : nadd) : (term477 n i x) = (term479 n i x).
Proof. exact (TRANS (@lem1297833 n i x) (@lem1297836 n i x)). Qed.
Lemma lem1297838 (n : nat) (i : nat) (x : nadd) : (term479 n i x) = (term477 n i x).
Proof. exact (SYM (@lem1297837 n i x)). Qed.
Lemma lem1297840 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term182 x y x' y'.
Proof. exact (EQ_MP (@lem1296708 x y x' y') (@lem1296707 x y x' y')). Qed.
Lemma lem1297841 (n : nat) (i : nat) (x : nadd) : term480 n i x.
Proof. exact (@lem1297840 (term348 i n) x (term348 n i) x). Qed.
Lemma lem1297845 (y : nadd) (x : nadd) : (term173 y x) = True.
Proof. exact (EQ_MP (@lem1296671 y x) (@lem1296670 y x)). Qed.
Lemma lem1297846 (n : nat) (i : nat) : (term481 n i) = True.
Proof. exact (@lem1297845 (nadd_of_num n) (nadd_of_num i)). Qed.
Lemma lem1297847 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1297848 (n : nat) (i : nat) : (term482 n i) = (and True).
Proof. exact (MK_COMB (@lem1297847) (@lem1297846 n i)). Qed.
Lemma lem1297850 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1296663 x) (@lem1296662 x)). Qed.
Lemma lem1297851 (n : nat) (i : nat) (x : nadd) : (term483 n i x) = (True /\ True).
Proof. exact (MK_COMB (@lem1297848 n i) (@lem1297850 x)). Qed.
Lemma lem1297853 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1297854 : (True /\ True) = True.
Proof. exact (@lem1297853 True). Qed.
Lemma lem1297855 (n : nat) (i : nat) (x : nadd) : (term483 n i x) = True.
Proof. exact (TRANS (@lem1297851 n i x) (@lem1297854)). Qed.
Lemma lem1297856 (n : nat) (i : nat) (x : nadd) : True = (term483 n i x).
Proof. exact (SYM (@lem1297855 n i x)). Qed.
Lemma lem1297857 (n : nat) (i : nat) (x : nadd) : term483 n i x.
Proof. exact (EQ_MP (@lem1297856 n i x) (@lem0)). Qed.
Lemma lem1297858 (n : nat) (i : nat) (x : nadd) : term479 n i x.
Proof. exact (@lem1297841 n i x (@lem1297857 n i x)). Qed.
Lemma lem1297859 (n : nat) (i : nat) (x : nadd) : term477 n i x.
Proof. exact (EQ_MP (@lem1297838 n i x) (@lem1297858 n i x)). Qed.
Lemma lem1297860 (n : nat) (i : nat) (x : nadd) : term484 n i x.
Proof. exact (ex_intro (term485 n i x) (term474 n i x) (@lem1297859 n i x)). Qed.
Lemma lem1297861 (n : nat) (i : nat) (x : nadd) : term470 n i x.
Proof. exact (@lem1297826 n i x (@lem1297860 n i x)). Qed.
Lemma lem1297862 (n : nat) (i : nat) (x : nadd) : term471 n i x.
Proof. exact (EQ_MP (@lem1297823 n i x) (@lem1297861 n i x)). Qed.
Lemma lem1297863 (n : nat) (i : nat) (x : nadd) : term486 n i x.
Proof. exact (ex_intro (term487 n i x) (term474 i n x) (@lem1297862 n i x)). Qed.
Lemma lem1297864 (n : nat) (i : nat) (x : nadd) : term488 n i x.
Proof. exact (@lem1297809 n i x (@lem1297863 n i x)). Qed.
Lemma lem1297865 (n : nat) (i : nat) (x : nadd) : term489 n i x.
Proof. exact (@lem1297806 n i x (@lem1297864 n i x)). Qed.
Lemma lem1297867 (y : nadd) (x : nadd) (z : nadd) : term6 y x z.
Proof. exact (EQ_MP (@lem1296658 y x z) (@lem1296657 y x z)). Qed.
Lemma lem1297868 (x : nadd) (n : nat) (r : nat -> nat) (i : nat) : term490 x n r i.
Proof. exact (@lem1297867 (term247 i x) (nadd_of_num n) (term250 r i)). Qed.
Lemma lem1297869 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term437 P r.
Proof. exact (h1). Qed.
Lemma lem1297870 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term491 P r n.
Proof. exact (@lem1297869 P r h1 n). Qed.
Lemma lem1297871 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term491 P r n) = (term436 P r n).
Proof. exact (eq_refl (term491 P r n)). Qed.
Lemma lem1297872 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term436 P r n.
Proof. exact (EQ_MP (@lem1297871 P r n) (@lem1297870 n P r h1)). Qed.
Lemma lem1297873 (n : nat) (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term492 P r n x.
Proof. exact (@lem1297872 n P r h1 x). Qed.
Lemma lem1297874 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (n : nat) : (term492 P r n x) = (term435 P x r n).
Proof. exact (eq_refl (term492 P r n x)). Qed.
Lemma lem1297875 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term435 P x r n.
Proof. exact (EQ_MP (@lem1297874 P x r n) (@lem1297873 n x P r h1)). Qed.
Lemma lem1297876 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1297877 (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term437 P r) (h2 : P x) : term434 x r n.
Proof. exact (@lem1297875 x n P r h1 (@lem1297876 P x h2)). Qed.
Lemma lem1297878 (r : nat -> nat) (n : nat) (P : nadd -> Prop) (x : nadd) (h1 : P x) : term493 P x r n.
Proof. exact (fun h0 : term437 P r => @lem1297877 n r P x h0 h1). Qed.
Lemma lem1297879 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term437 P r.
Proof. exact (h1). Qed.
Lemma lem1297880 (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term437 P r) (h2 : P x) : term434 x r n.
Proof. exact (@lem1297878 r n P x h2 (@lem1297879 P r h1)). Qed.
Lemma lem1297881 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term435 P x r n.
Proof. exact (fun h0 : P x => @lem1297880 n r P x h1 h0). Qed.
Lemma lem1297882 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term494 P x r.
Proof. exact (fun n : nat => @lem1297881 x n P r h1). Qed.
Lemma lem1297883 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term495 P r.
Proof. exact (fun x : nadd => @lem1297882 x P r h1). Qed.
Lemma lem1297884 (P : nadd -> Prop) (r : nat -> nat) : term496 P r.
Proof. exact (fun h0 : term437 P r => @lem1297883 P r h0). Qed.
Lemma lem1297885 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term495 P r.
Proof. exact (@lem1297884 P r (@lem1297726 P r h1)). Qed.
Lemma lem1297886 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term497 P r x.
Proof. exact (@lem1297885 P r h1 x). Qed.
Lemma lem1297887 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) : (term497 P r x) = (term494 P x r).
Proof. exact (eq_refl (term497 P r x)). Qed.
Lemma lem1297888 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term494 P x r.
Proof. exact (EQ_MP (@lem1297887 P x r) (@lem1297886 x P r h1)). Qed.
Lemma lem1297889 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term498 P x r n.
Proof. exact (@lem1297888 x P r h1 n). Qed.
Lemma lem1297890 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (n : nat) : (term498 P x r n) = (term435 P x r n).
Proof. exact (eq_refl (term498 P x r n)). Qed.
Lemma lem1297893 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term435 P x r n.
Proof. exact (EQ_MP (@lem1297890 P x r n) (@lem1297889 x n P r h1)). Qed.
Lemma lem1297894 (x : nadd) (i : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term435 P x r i.
Proof. exact (@lem1297893 x i P r h1). Qed.
Lemma lem1297915 (P : nadd -> Prop) (x : nadd) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1297920 (P : nadd -> Prop) (x : nadd) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1297915 P x) (@lem1297734 P x h1)). Qed.
Lemma lem1297921 (P : nadd -> Prop) (x : nadd) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1297920 P x h1)). Qed.
Lemma lem1297922 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1297921 P x h1) (@lem0)). Qed.
Lemma lem1297923 (i : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term434 x r i.
Proof. exact (@lem1297894 x i P r h1 (@lem1297922 P x h2)). Qed.
Lemma lem1297924 (n : nat) (i : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term499 x n r i.
Proof. exact (@lem1297868 x n r i (@lem1297923 i r P x h1 h2)). Qed.
Lemma lem1297925 (n : nat) (i : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term500 x n r i.
Proof. exact (conj (@lem1297865 n i x) (@lem1297924 n i r P x h1 h2)). Qed.
Lemma lem1297926 (n : nat) (i : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term501 x n r i.
Proof. exact (ex_intro (term502 x n r i) (term450 n i x) (@lem1297925 n i r P x h1 h2)). Qed.
Lemma lem1297927 (n : nat) (i : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term503 x n r i.
Proof. exact (@lem1297803 x n r i (@lem1297926 n i r P x h1 h2)). Qed.
Lemma lem1297929 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1296628 n m) (@lem1296627 m n)). Qed.
Lemma lem1297930 (n : nat) (r : nat -> nat) (i : nat) : (term445 r i n) = (term504 n r i).
Proof. exact (@lem1297929 n (term444 n r i)). Qed.
Lemma lem1297931 : nadd_of_num = nadd_of_num.
Proof. exact (eq_refl nadd_of_num). Qed.
Lemma lem1297932 (n : nat) (r : nat -> nat) (i : nat) : (term448 r i n) = (term505 n r i).
Proof. exact (MK_COMB (@lem1297931) (@lem1297930 n r i)). Qed.
Lemma lem1297933 (n : nat) (r : nat -> nat) (i : nat) : (term506 n r i) = (term506 n r i).
Proof. exact (eq_refl (term506 n r i)). Qed.
Lemma lem1297934 (n : nat) (r : nat -> nat) (i : nat) : (term507 r i n) = (term508 n r i).
Proof. exact (MK_COMB (@lem1297933 n r i) (@lem1297932 n r i)). Qed.
Lemma lem1297935 (r : nat -> nat) (i : nat) (n : nat) : (term508 n r i) = (term507 r i n).
Proof. exact (SYM (@lem1297934 n r i)). Qed.
Lemma lem1297937 (m : nat) (n : nat) : (term158 m n) = (term157 m n).
Proof. exact (EQ_MP (@lem1296622 m n) (@lem1296621 m n)). Qed.
Lemma lem1297938 (n : nat) (r : nat -> nat) (i : nat) : (term504 n r i) = (term509 n r i).
Proof. exact (@lem1297937 n (r i)). Qed.
Lemma lem1297939 : nadd_of_num = nadd_of_num.
Proof. exact (eq_refl nadd_of_num). Qed.
Lemma lem1297940 (n : nat) (r : nat -> nat) (i : nat) : (term505 n r i) = (term510 n r i).
Proof. exact (MK_COMB (@lem1297939) (@lem1297938 n r i)). Qed.
Lemma lem1297941 (n : nat) (r : nat -> nat) (i : nat) : (term506 n r i) = (term506 n r i).
Proof. exact (eq_refl (term506 n r i)). Qed.
Lemma lem1297942 (n : nat) (r : nat -> nat) (i : nat) : (term508 n r i) = (term511 n r i).
Proof. exact (MK_COMB (@lem1297941 n r i) (@lem1297940 n r i)). Qed.
Lemma lem1297943 (n : nat) (r : nat -> nat) (i : nat) : (term511 n r i) = (term508 n r i).
Proof. exact (SYM (@lem1297942 n r i)). Qed.
Lemma lem1297945 (x : nadd) (y : nadd) : term154 x y.
Proof. exact (EQ_MP (@lem1296602 x y) (@lem1296601 x y)). Qed.
Lemma lem1297946 (n : nat) (r : nat -> nat) (i : nat) : term512 n r i.
Proof. exact (@lem1297945 (term465 n r i) (term510 n r i)). Qed.
Lemma lem1297948 (m : nat) (n : nat) : (term149 m n) = True.
Proof. exact (EQ_MP (@lem1296579 m n) (@lem1296578 m n)). Qed.
Lemma lem1297949 (n : nat) (r : nat -> nat) (i : nat) : (term513 n r i) = True.
Proof. exact (@lem1297948 n (term395 r i)). Qed.
Lemma lem1297950 (n : nat) (r : nat -> nat) (i : nat) : True = (term513 n r i).
Proof. exact (SYM (@lem1297949 n r i)). Qed.
Lemma lem1297951 (n : nat) (r : nat -> nat) (i : nat) : term513 n r i.
Proof. exact (EQ_MP (@lem1297950 n r i) (@lem0)). Qed.
Lemma lem1297952 (n : nat) (r : nat -> nat) (i : nat) : term511 n r i.
Proof. exact (@lem1297946 n r i (@lem1297951 n r i)). Qed.
Lemma lem1297953 (n : nat) (r : nat -> nat) (i : nat) : term508 n r i.
Proof. exact (EQ_MP (@lem1297943 n r i) (@lem1297952 n r i)). Qed.
Lemma lem1297954 (r : nat -> nat) (i : nat) (n : nat) : term507 r i n.
Proof. exact (EQ_MP (@lem1297935 r i n) (@lem1297953 n r i)). Qed.
Lemma lem1297955 (i : nat) (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term514 x r i n.
Proof. exact (conj (@lem1297927 n i r P x h1 h2) (@lem1297954 r i n)). Qed.
Lemma lem1297956 (i : nat) (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term515 x r i n.
Proof. exact (ex_intro (term516 x r i n) (term465 n r i) (@lem1297955 i n r P x h1 h2)). Qed.
Lemma lem1297957 (i : nat) (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term517 x r i n.
Proof. exact (@lem1297800 x r i n (@lem1297956 i n r P x h1 h2)). Qed.
Lemma lem1297958 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term518 x r i n.
Proof. exact (conj (@lem1297797 i r n x h3) (@lem1297957 i n r P x h1 h2)). Qed.
Lemma lem1297959 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term519 r i n.
Proof. exact (ex_intro (term520 r i n) (term450 i n x) (@lem1297958 i P r n x h1 h2 h3)). Qed.
Lemma lem1297960 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term443 r i n.
Proof. exact (@lem1297741 r i n (@lem1297959 i P r n x h1 h2 h3)). Qed.
Lemma lem1297961 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term442 r i n.
Proof. exact (EQ_MP (@lem1297738 r i n) (@lem1297960 i P r n x h1 h2 h3)). Qed.
Lemma lem1297962 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : term441 r n x.
Proof. exact (proj2 (@lem1297732 P r n x h1)). Qed.
Lemma lem1297963 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : P x.
Proof. exact (proj1 (@lem1297732 P r n x h1)). Qed.
Lemma lem1297964 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : (term441 r n x) = (term442 r i n).
Proof. exact (prop_ext (fun h4 : term441 r n x => @lem1297961 i P r n x h1 h2 h3) (fun h4 : term442 r i n => @lem1297733 r n x h3)). Qed.
Lemma lem1297965 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term442 r i n.
Proof. exact (EQ_MP (@lem1297964 i P r n x h1 h2 h3) (@lem1297733 r n x h3)). Qed.
Lemma lem1297966 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : (P x) = (term442 r i n).
Proof. exact (prop_ext (fun h4 : P x => @lem1297965 i P r n x h1 h2 h3) (fun h4 : term442 r i n => @lem1297734 P x h2)). Qed.
Lemma lem1297967 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term441 r n x) : term442 r i n.
Proof. exact (EQ_MP (@lem1297966 i P r n x h1 h2 h3) (@lem1297734 P x h2)). Qed.
Lemma lem1297968 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term440 P r n x) : (term441 r n x) = (term442 r i n).
Proof. exact (prop_ext (fun h4 : term441 r n x => @lem1297967 i P r n x h1 h2 h4) (fun h4 : term442 r i n => @lem1297962 P r n x h3)). Qed.
Lemma lem1297969 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : P x) (h3 : term440 P r n x) : term442 r i n.
Proof. exact (EQ_MP (@lem1297968 i P r n x h1 h2 h3) (@lem1297962 P r n x h3)). Qed.
Lemma lem1297970 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : term440 P r n x) : (P x) = (term442 r i n).
Proof. exact (prop_ext (fun h3 : P x => @lem1297969 i P r n x h1 h3 h2) (fun h3 : term442 r i n => @lem1297963 P r n x h2)). Qed.
Lemma lem1297971 (i : nat) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term422 P r) (h2 : term440 P r n x) : term442 r i n.
Proof. exact (EQ_MP (@lem1297970 i P r n x h1 h2) (@lem1297963 P r n x h2)). Qed.
Lemma lem1297972 (i : nat) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term391 P r) : term442 r i n.
Proof. exact (ex_elim (@lem1297731 n P r h2) (fun x : nadd => fun h0 : term521 P r n x => @lem1297971 i P r n x h1 h0)). Qed.
Lemma lem1297977 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term391 P r) : term522 r n.
Proof. exact (fun i : nat => @lem1297972 i n P r h1 h2). Qed.
Lemma lem1297982 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term391 P r) : term438 r.
Proof. exact (fun n : nat => @lem1297977 n P r h1 h2). Qed.
Lemma lem1297983 (r : nat -> nat) (h1 : (term145 r) = r) : (term145 r) = r.
Proof. exact (h1). Qed.
Lemma lem1297985 (r : nat -> nat) : ((term145 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1296571 r) (@lem1262760 r)). Qed.
Lemma lem1297986 (r : nat -> nat) : (is_nadd r) = ((term145 r) = r).
Proof. exact (SYM (@lem1297985 r)). Qed.
Lemma lem1297988 (x : nat -> nat) : (is_nadd x) = (term144 x).
Proof. exact (EQ_MP (@lem1296565 x) (@lem1296564 x)). Qed.
Lemma lem1297989 (r : nat -> nat) : (is_nadd r) = (term144 r).
Proof. exact (@lem1297988 r). Qed.
Lemma lem1298003 (n : nat) (m : nat) (p : nat) : (term141 m n p) = (term142 n m p).
Proof. exact (EQ_MP (@lem1296562 n m p) (@lem1296561 n m p)). Qed.
Lemma lem1298004 (r : nat -> nat) (B : nat) (m : nat) (n : nat) : (term523 r B m n) = (term524 r B m n).
Proof. exact (@lem1298003 (term444 n r m) (term444 m r n) (term525 B m n)). Qed.
Lemma lem1298007 (r : nat -> nat) (B : nat) (m : nat) : (term526 r B m) = (term527 r B m).
Proof. exact (fun_ext (fun n : nat => @lem1298004 r B m n)). Qed.
Lemma lem1298008 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298009 (r : nat -> nat) (B : nat) (m : nat) : (term528 r B m) = (term529 r B m).
Proof. exact (MK_COMB (@lem1298008) (@lem1298007 r B m)). Qed.
Lemma lem1298014 (r : nat -> nat) (B : nat) : (term530 r B) = (term531 r B).
Proof. exact (fun_ext (fun m : nat => @lem1298009 r B m)). Qed.
Lemma lem1298015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298016 (r : nat -> nat) (B : nat) : (term532 r B) = (term533 r B).
Proof. exact (MK_COMB (@lem1298015) (@lem1298014 r B)). Qed.
Lemma lem1298021 (r : nat -> nat) : (term534 r) = (term535 r).
Proof. exact (fun_ext (fun B : nat => @lem1298016 r B)). Qed.
Lemma lem1298022 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298023 (r : nat -> nat) : (term144 r) = (term536 r).
Proof. exact (MK_COMB (@lem1298022) (@lem1298021 r)). Qed.
Lemma lem1298028 (r : nat -> nat) : (is_nadd r) = (term536 r).
Proof. exact (TRANS (@lem1297989 r) (@lem1298023 r)). Qed.
Lemma lem1298029 (r : nat -> nat) : (term536 r) = (is_nadd r).
Proof. exact (SYM (@lem1298028 r)). Qed.
Lemma lem1298041 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem1296545 n) (@lem1296544 n)). Qed.
Lemma lem1298042 (m : nat) (n : nat) : (term537 m n) = (Nat.add m n).
Proof. exact (@lem1298041 (Nat.add m n)). Qed.
Lemma lem1298043 (n : nat) (r : nat -> nat) (m : nat) : (term538 n r m) = (term538 n r m).
Proof. exact (eq_refl (term538 n r m)). Qed.
Lemma lem1298044 (r : nat -> nat) (m : nat) (n : nat) : (term539 r m n) = (term540 r m n).
Proof. exact (MK_COMB (@lem1298043 n r m) (@lem1298042 m n)). Qed.
Lemma lem1298045 (m : nat) (r : nat -> nat) (n : nat) : (term541 m r n) = (term541 m r n).
Proof. exact (eq_refl (term541 m r n)). Qed.
Lemma lem1298046 (r : nat -> nat) (m : nat) (n : nat) : (term542 r m n) = (term543 r m n).
Proof. exact (MK_COMB (@lem1298045 m r n) (@lem1298044 r m n)). Qed.
Lemma lem1298047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298048 (r : nat -> nat) (m : nat) (n : nat) : (term544 r m n) = (term545 r m n).
Proof. exact (MK_COMB (@lem1298047) (@lem1298046 r m n)). Qed.
Lemma lem1298050 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem1296545 n) (@lem1296544 n)). Qed.
Lemma lem1298051 (m : nat) (n : nat) : (term537 m n) = (Nat.add m n).
Proof. exact (@lem1298050 (Nat.add m n)). Qed.
Lemma lem1298052 (m : nat) (r : nat -> nat) (n : nat) : (term538 m r n) = (term538 m r n).
Proof. exact (eq_refl (term538 m r n)). Qed.
Lemma lem1298053 (r : nat -> nat) (m : nat) (n : nat) : (term546 r m n) = (term547 r m n).
Proof. exact (MK_COMB (@lem1298052 m r n) (@lem1298051 m n)). Qed.
Lemma lem1298054 (n : nat) (r : nat -> nat) (m : nat) : (term541 n r m) = (term541 n r m).
Proof. exact (eq_refl (term541 n r m)). Qed.
Lemma lem1298055 (r : nat -> nat) (m : nat) (n : nat) : (term548 r m n) = (term549 r m n).
Proof. exact (MK_COMB (@lem1298054 n r m) (@lem1298053 r m n)). Qed.
Lemma lem1298056 (r : nat -> nat) (m : nat) (n : nat) : (term550 r m n) = (term551 r m n).
Proof. exact (MK_COMB (@lem1298048 r m n) (@lem1298055 r m n)). Qed.
Lemma lem1298059 (r : nat -> nat) (m : nat) : (term552 r m) = (term553 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298056 r m n)). Qed.
Lemma lem1298060 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298061 (r : nat -> nat) (m : nat) : (term554 r m) = (term555 r m).
Proof. exact (MK_COMB (@lem1298060) (@lem1298059 r m)). Qed.
Lemma lem1298066 (r : nat -> nat) : (term556 r) = (term557 r).
Proof. exact (fun_ext (fun m : nat => @lem1298061 r m)). Qed.
Lemma lem1298067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298068 (r : nat -> nat) : (term558 r) = (term559 r).
Proof. exact (MK_COMB (@lem1298067) (@lem1298066 r)). Qed.
Lemma lem1298073 (r : nat -> nat) : (term559 r) = (term558 r).
Proof. exact (SYM (@lem1298068 r)). Qed.
Lemma lem1298079 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem1296519 A P Q) (@lem1296518 A P Q)). Qed.
Lemma lem1298080 (P : nat -> Prop) (Q : nat -> Prop) : (term560 P Q) = (term561 P Q).
Proof. exact (@lem1298079 nat P Q). Qed.
Lemma lem1298081 (r : nat -> nat) (m : nat) : (term562 r m) = (term563 r m).
Proof. exact (@lem1298080 (term564 r m) (term565 r m)). Qed.
Lemma lem1298082 (r : nat -> nat) (m : nat) (n : nat) : (term566 r m n) = (term543 r m n).
Proof. exact (eq_refl (term566 r m n)). Qed.
Lemma lem1298083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298084 (r : nat -> nat) (m : nat) (n : nat) : (term567 r m n) = (term545 r m n).
Proof. exact (MK_COMB (@lem1298083) (@lem1298082 r m n)). Qed.
Lemma lem1298085 (r : nat -> nat) (m : nat) (n : nat) : (term568 r m n) = (term549 r m n).
Proof. exact (eq_refl (term568 r m n)). Qed.
Lemma lem1298086 (r : nat -> nat) (m : nat) (n : nat) : (term569 r m n) = (term551 r m n).
Proof. exact (MK_COMB (@lem1298084 r m n) (@lem1298085 r m n)). Qed.
Lemma lem1298087 (r : nat -> nat) (m : nat) : (term570 r m) = (term553 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298086 r m n)). Qed.
Lemma lem1298088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298089 (r : nat -> nat) (m : nat) : (term562 r m) = (term555 r m).
Proof. exact (MK_COMB (@lem1298088) (@lem1298087 r m)). Qed.
Lemma lem1298090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1298091 (r : nat -> nat) (m : nat) : (term571 r m) = (term572 r m).
Proof. exact (MK_COMB (@lem1298090) (@lem1298089 r m)). Qed.
Lemma lem1298092 (r : nat -> nat) (m : nat) (n : nat) : (term566 r m n) = (term543 r m n).
Proof. exact (eq_refl (term566 r m n)). Qed.
Lemma lem1298093 (r : nat -> nat) (m : nat) : (term573 r m) = (term564 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298092 r m n)). Qed.
Lemma lem1298094 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298095 (r : nat -> nat) (m : nat) : (term574 r m) = (term575 r m).
Proof. exact (MK_COMB (@lem1298094) (@lem1298093 r m)). Qed.
Lemma lem1298096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298097 (r : nat -> nat) (m : nat) : (term576 r m) = (term577 r m).
Proof. exact (MK_COMB (@lem1298096) (@lem1298095 r m)). Qed.
Lemma lem1298098 (r : nat -> nat) (m : nat) (n : nat) : (term568 r m n) = (term549 r m n).
Proof. exact (eq_refl (term568 r m n)). Qed.
Lemma lem1298099 (r : nat -> nat) (m : nat) : (term578 r m) = (term565 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298098 r m n)). Qed.
Lemma lem1298100 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298101 (r : nat -> nat) (m : nat) : (term579 r m) = (term580 r m).
Proof. exact (MK_COMB (@lem1298100) (@lem1298099 r m)). Qed.
Lemma lem1298102 (r : nat -> nat) (m : nat) : (term563 r m) = (term581 r m).
Proof. exact (MK_COMB (@lem1298097 r m) (@lem1298101 r m)). Qed.
Lemma lem1298103 (r : nat -> nat) (m : nat) : ((term562 r m) = (term563 r m)) = ((term555 r m) = (term581 r m)).
Proof. exact (MK_COMB (@lem1298091 r m) (@lem1298102 r m)). Qed.
Lemma lem1298104 (r : nat -> nat) (m : nat) : (term555 r m) = (term581 r m).
Proof. exact (EQ_MP (@lem1298103 r m) (@lem1298081 r m)). Qed.
Lemma lem1298115 (r : nat -> nat) : (term557 r) = (term582 r).
Proof. exact (fun_ext (fun m : nat => @lem1298104 r m)). Qed.
Lemma lem1298116 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298117 (r : nat -> nat) : (term559 r) = (term583 r).
Proof. exact (MK_COMB (@lem1298116) (@lem1298115 r)). Qed.
Lemma lem1298119 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem1296519 A P Q) (@lem1296518 A P Q)). Qed.
Lemma lem1298120 (P : nat -> Prop) (Q : nat -> Prop) : (term560 P Q) = (term561 P Q).
Proof. exact (@lem1298119 nat P Q). Qed.
Lemma lem1298121 (r : nat -> nat) : (term584 r) = (term585 r).
Proof. exact (@lem1298120 (term586 r) (term587 r)). Qed.
Lemma lem1298122 (r : nat -> nat) (m : nat) : (term588 r m) = (term575 r m).
Proof. exact (eq_refl (term588 r m)). Qed.
Lemma lem1298123 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298124 (r : nat -> nat) (m : nat) : (term589 r m) = (term577 r m).
Proof. exact (MK_COMB (@lem1298123) (@lem1298122 r m)). Qed.
Lemma lem1298125 (r : nat -> nat) (m : nat) : (term590 r m) = (term580 r m).
Proof. exact (eq_refl (term590 r m)). Qed.
Lemma lem1298126 (r : nat -> nat) (m : nat) : (term591 r m) = (term581 r m).
Proof. exact (MK_COMB (@lem1298124 r m) (@lem1298125 r m)). Qed.
Lemma lem1298127 (r : nat -> nat) : (term592 r) = (term582 r).
Proof. exact (fun_ext (fun m : nat => @lem1298126 r m)). Qed.
Lemma lem1298128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298129 (r : nat -> nat) : (term584 r) = (term583 r).
Proof. exact (MK_COMB (@lem1298128) (@lem1298127 r)). Qed.
Lemma lem1298130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1298131 (r : nat -> nat) : (term593 r) = (term594 r).
Proof. exact (MK_COMB (@lem1298130) (@lem1298129 r)). Qed.
Lemma lem1298132 (r : nat -> nat) (m : nat) : (term588 r m) = (term575 r m).
Proof. exact (eq_refl (term588 r m)). Qed.
Lemma lem1298133 (r : nat -> nat) : (term595 r) = (term586 r).
Proof. exact (fun_ext (fun m : nat => @lem1298132 r m)). Qed.
Lemma lem1298134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298135 (r : nat -> nat) : (term596 r) = (term597 r).
Proof. exact (MK_COMB (@lem1298134) (@lem1298133 r)). Qed.
Lemma lem1298136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298137 (r : nat -> nat) : (term598 r) = (term599 r).
Proof. exact (MK_COMB (@lem1298136) (@lem1298135 r)). Qed.
Lemma lem1298138 (r : nat -> nat) (m : nat) : (term590 r m) = (term580 r m).
Proof. exact (eq_refl (term590 r m)). Qed.
Lemma lem1298139 (r : nat -> nat) : (term600 r) = (term587 r).
Proof. exact (fun_ext (fun m : nat => @lem1298138 r m)). Qed.
Lemma lem1298140 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298141 (r : nat -> nat) : (term601 r) = (term602 r).
Proof. exact (MK_COMB (@lem1298140) (@lem1298139 r)). Qed.
Lemma lem1298142 (r : nat -> nat) : (term585 r) = (term603 r).
Proof. exact (MK_COMB (@lem1298137 r) (@lem1298141 r)). Qed.
Lemma lem1298143 (r : nat -> nat) : ((term584 r) = (term585 r)) = ((term583 r) = (term603 r)).
Proof. exact (MK_COMB (@lem1298131 r) (@lem1298142 r)). Qed.
Lemma lem1298144 (r : nat -> nat) : (term583 r) = (term603 r).
Proof. exact (EQ_MP (@lem1298143 r) (@lem1298121 r)). Qed.
Lemma lem1298163 (r : nat -> nat) : (term559 r) = (term603 r).
Proof. exact (TRANS (@lem1298117 r) (@lem1298144 r)). Qed.
Lemma lem1298164 (r : nat -> nat) : (term603 r) = (term559 r).
Proof. exact (SYM (@lem1298163 r)). Qed.
Lemma lem1298166 {A B : Type'} (P : type1413 A B) : (term129 A B P) = (term130 A B P).
Proof. exact (EQ_MP (@lem1296513 A B P) (@lem1296512 A B P)). Qed.
Lemma lem1298167 (P : type1605) : (term604 P) = (term605 P).
Proof. exact (@lem1298166 nat nat P). Qed.
Lemma lem1298168 (r : nat -> nat) : (term606 r) = (term607 r).
Proof. exact (@lem1298167 (term608 r)). Qed.
Lemma lem1298169 (r : nat -> nat) (m : nat) : (term609 r m) = (term565 r m).
Proof. exact (eq_refl (term609 r m)). Qed.
Lemma lem1298170 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1298171 (r : nat -> nat) (m : nat) (n : nat) : (term610 r m n) = (term568 r m n).
Proof. exact (MK_COMB (@lem1298169 r m) (@lem1298170 n)). Qed.
Lemma lem1298172 (r : nat -> nat) (m : nat) (n : nat) : (term568 r m n) = (term549 r m n).
Proof. exact (eq_refl (term568 r m n)). Qed.
Lemma lem1298173 (r : nat -> nat) (m : nat) (n : nat) : (term610 r m n) = (term549 r m n).
Proof. exact (TRANS (@lem1298171 r m n) (@lem1298172 r m n)). Qed.
Lemma lem1298174 (r : nat -> nat) (m : nat) : (term611 r m) = (term565 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298173 r m n)). Qed.
Lemma lem1298175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298176 (r : nat -> nat) (m : nat) : (term612 r m) = (term580 r m).
Proof. exact (MK_COMB (@lem1298175) (@lem1298174 r m)). Qed.
Lemma lem1298177 (r : nat -> nat) : (term613 r) = (term587 r).
Proof. exact (fun_ext (fun m : nat => @lem1298176 r m)). Qed.
Lemma lem1298178 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298179 (r : nat -> nat) : (term606 r) = (term602 r).
Proof. exact (MK_COMB (@lem1298178) (@lem1298177 r)). Qed.
Lemma lem1298180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1298181 (r : nat -> nat) : (term614 r) = (term615 r).
Proof. exact (MK_COMB (@lem1298180) (@lem1298179 r)). Qed.
Lemma lem1298182 (r : nat -> nat) (m : nat) : (term609 r m) = (term565 r m).
Proof. exact (eq_refl (term609 r m)). Qed.
Lemma lem1298183 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1298184 (r : nat -> nat) (m : nat) (n : nat) : (term610 r m n) = (term568 r m n).
Proof. exact (MK_COMB (@lem1298182 r m) (@lem1298183 n)). Qed.
Lemma lem1298185 (r : nat -> nat) (m : nat) (n : nat) : (term568 r m n) = (term549 r m n).
Proof. exact (eq_refl (term568 r m n)). Qed.
Lemma lem1298186 (r : nat -> nat) (m : nat) (n : nat) : (term610 r m n) = (term549 r m n).
Proof. exact (TRANS (@lem1298184 r m n) (@lem1298185 r m n)). Qed.
Lemma lem1298187 (r : nat -> nat) (n : nat) : (term616 r n) = (term617 r n).
Proof. exact (fun_ext (fun m : nat => @lem1298186 r m n)). Qed.
Lemma lem1298188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298189 (r : nat -> nat) (n : nat) : (term618 r n) = (term619 r n).
Proof. exact (MK_COMB (@lem1298188) (@lem1298187 r n)). Qed.
Lemma lem1298190 (r : nat -> nat) : (term620 r) = (term621 r).
Proof. exact (fun_ext (fun n : nat => @lem1298189 r n)). Qed.
Lemma lem1298191 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298192 (r : nat -> nat) : (term607 r) = (term622 r).
Proof. exact (MK_COMB (@lem1298191) (@lem1298190 r)). Qed.
Lemma lem1298193 (r : nat -> nat) : ((term606 r) = (term607 r)) = ((term602 r) = (term622 r)).
Proof. exact (MK_COMB (@lem1298181 r) (@lem1298192 r)). Qed.
Lemma lem1298194 (r : nat -> nat) : (term602 r) = (term622 r).
Proof. exact (EQ_MP (@lem1298193 r) (@lem1298168 r)). Qed.
Lemma lem1298195 (r : nat -> nat) : (term599 r) = (term599 r).
Proof. exact (eq_refl (term599 r)). Qed.
Lemma lem1298196 (r : nat -> nat) : (term603 r) = (term623 r).
Proof. exact (MK_COMB (@lem1298195 r) (@lem1298194 r)). Qed.
Lemma lem1298197 (r : nat -> nat) : (term623 r) = (term603 r).
Proof. exact (SYM (@lem1298196 r)). Qed.
Lemma lem1298199 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1296510 n m) (@lem1296509 m n)). Qed.
Lemma lem1298200 (n : nat) (r : nat -> nat) (m : nat) : (term538 n r m) = (term538 n r m).
Proof. exact (eq_refl (term538 n r m)). Qed.
Lemma lem1298201 (r : nat -> nat) (n : nat) (m : nat) : (term540 r m n) = (term547 r n m).
Proof. exact (MK_COMB (@lem1298200 n r m) (@lem1298199 n m)). Qed.
Lemma lem1298202 (m : nat) (r : nat -> nat) (n : nat) : (term541 m r n) = (term541 m r n).
Proof. exact (eq_refl (term541 m r n)). Qed.
Lemma lem1298203 (r : nat -> nat) (n : nat) (m : nat) : (term543 r m n) = (term549 r n m).
Proof. exact (MK_COMB (@lem1298202 m r n) (@lem1298201 r n m)). Qed.
Lemma lem1298204 (r : nat -> nat) (m : nat) : (term564 r m) = (term617 r m).
Proof. exact (fun_ext (fun n : nat => @lem1298203 r n m)). Qed.
Lemma lem1298205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298206 (r : nat -> nat) (m : nat) : (term575 r m) = (term619 r m).
Proof. exact (MK_COMB (@lem1298205) (@lem1298204 r m)). Qed.
Lemma lem1298207 (r : nat -> nat) : (term586 r) = (term621 r).
Proof. exact (fun_ext (fun m : nat => @lem1298206 r m)). Qed.
Lemma lem1298208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298209 (r : nat -> nat) : (term597 r) = (term622 r).
Proof. exact (MK_COMB (@lem1298208) (@lem1298207 r)). Qed.
Lemma lem1298210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298211 (r : nat -> nat) : (term599 r) = (term624 r).
Proof. exact (MK_COMB (@lem1298210) (@lem1298209 r)). Qed.
Lemma lem1298212 (r : nat -> nat) : (term622 r) = (term622 r).
Proof. exact (eq_refl (term622 r)). Qed.
Lemma lem1298213 (r : nat -> nat) : (term623 r) = (term625 r).
Proof. exact (MK_COMB (@lem1298211 r) (@lem1298212 r)). Qed.
Lemma lem1298214 (r : nat -> nat) : (term625 r) = (term623 r).
Proof. exact (SYM (@lem1298213 r)). Qed.
Lemma lem1298216 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem1298217 (r : nat -> nat) : (term625 r) = (term622 r).
Proof. exact (@lem1298216 (term622 r)). Qed.
Lemma lem1298220 (r : nat -> nat) : (term626 r) = (term626 r).
Proof. exact (eq_refl (term626 r)). Qed.
Lemma lem1298221 (r : nat -> nat) : (term626 r) = ((term625 r) = (term622 r)).
Proof. exact (eq_refl (term626 r)). Qed.
Lemma lem1298222 (r : nat -> nat) : (term627 r) = (term627 r).
Proof. exact (eq_refl (term627 r)). Qed.
Lemma lem1298223 (r : nat -> nat) : ((term626 r) = (term626 r)) = ((term626 r) = ((term625 r) = (term622 r))).
Proof. exact (MK_COMB (@lem1298222 r) (@lem1298221 r)). Qed.
Lemma lem1298224 (r : nat -> nat) : (term626 r) = ((term625 r) = (term622 r)).
Proof. exact (eq_refl (term626 r)). Qed.
Lemma lem1298225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1298226 (r : nat -> nat) : (term627 r) = (term628 r).
Proof. exact (MK_COMB (@lem1298225) (@lem1298224 r)). Qed.
Lemma lem1298227 (r : nat -> nat) : ((term625 r) = (term622 r)) = ((term625 r) = (term622 r)).
Proof. exact (eq_refl ((term625 r) = (term622 r))). Qed.
Lemma lem1298228 (r : nat -> nat) : ((term626 r) = ((term625 r) = (term622 r))) = (((term625 r) = (term622 r)) = ((term625 r) = (term622 r))).
Proof. exact (MK_COMB (@lem1298226 r) (@lem1298227 r)). Qed.
Lemma lem1298229 (r : nat -> nat) : ((term626 r) = (term626 r)) = (((term625 r) = (term622 r)) = ((term625 r) = (term622 r))).
Proof. exact (TRANS (@lem1298223 r) (@lem1298228 r)). Qed.
Lemma lem1298230 (r : nat -> nat) : ((term625 r) = (term622 r)) = ((term625 r) = (term622 r)).
Proof. exact (EQ_MP (@lem1298229 r) (@lem1298220 r)). Qed.
Lemma lem1298231 (r : nat -> nat) : (term625 r) = (term622 r).
Proof. exact (EQ_MP (@lem1298230 r) (@lem1298217 r)). Qed.
Lemma lem1298240 (r : nat -> nat) : (term622 r) = (term625 r).
Proof. exact (SYM (@lem1298231 r)). Qed.
Lemma lem1298242 (m : nat) (p : nat) : term77 m p.
Proof. exact (EQ_MP (@lem1296504 m p) (@lem1296503 m p)). Qed.
Lemma lem1298243 (r : nat -> nat) (n : nat) (i : nat) : term629 r n i.
Proof. exact (@lem1298242 (term444 i r n) (term547 r n i)). Qed.
Lemma lem1298244 (m : nat) : term630 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1298245 (m : nat) : (term630 m) = (term631 m).
Proof. exact (eq_refl (term630 m)). Qed.
Lemma lem1298246 (m : nat) : term631 m.
Proof. exact (EQ_MP (@lem1298245 m) (@lem1298244 m)). Qed.
Lemma lem1298247 (m : nat) (n : nat) : term632 m n.
Proof. exact (@lem1298246 m n). Qed.
Lemma lem1298248 (m : nat) (n : nat) : (term632 m n) = (term633 m n).
Proof. exact (eq_refl (term632 m n)). Qed.
Lemma lem1298249 (m : nat) (n : nat) : term633 m n.
Proof. exact (EQ_MP (@lem1298248 m n) (@lem1298247 m n)). Qed.
Lemma lem1298250 (m : nat) (n : nat) : (term633 m n) = ((term633 m n) = True).
Proof. exact (@lem7 (term633 m n)). Qed.
Lemma lem1298252 (m : nat) : term114 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1298253 (m : nat) : (term114 m) = (term99 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem1298254 (m : nat) : term99 m.
Proof. exact (EQ_MP (@lem1298253 m) (@lem1298252 m)). Qed.
Lemma lem1298255 (m : nat) (n : nat) : term115 m n.
Proof. exact (@lem1298254 m n). Qed.
Lemma lem1298256 (m : nat) (n : nat) : (term115 m n) = (term95 m n).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem1298257 (m : nat) (n : nat) : term95 m n.
Proof. exact (EQ_MP (@lem1298256 m n) (@lem1298255 m n)). Qed.
Lemma lem1298258 (m : nat) (n : nat) (p : nat) : term116 m n p.
Proof. exact (@lem1298257 m n p). Qed.
Lemma lem1298259 (m : nat) (n : nat) (p : nat) : (term116 m n p) = ((term91 m n p) = (term92 m n p)).
Proof. exact (eq_refl (term116 m n p)). Qed.
Lemma lem1298281 (n : nat) (r : nat -> nat) (h1 : term438 r) : term634 r n.
Proof. exact (@lem1297728 r h1 n). Qed.
Lemma lem1298282 (r : nat -> nat) (n : nat) : (term634 r n) = (term522 r n).
Proof. exact (eq_refl (term634 r n)). Qed.
Lemma lem1298283 (n : nat) (r : nat -> nat) (h1 : term438 r) : term522 r n.
Proof. exact (EQ_MP (@lem1298282 r n) (@lem1298281 n r h1)). Qed.
Lemma lem1298284 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term635 r n i.
Proof. exact (@lem1298283 n r h1 i). Qed.
Lemma lem1298285 (r : nat -> nat) (i : nat) (n : nat) : (term635 r n i) = (term442 r i n).
Proof. exact (eq_refl (term635 r n i)). Qed.
Lemma lem1298286 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : term442 r i n.
Proof. exact (EQ_MP (@lem1298285 r i n) (@lem1298284 n i r h1)). Qed.
Lemma lem1298287 (r : nat -> nat) (i : nat) (n : nat) : (term442 r i n) = ((term442 r i n) = True).
Proof. exact (@lem7 (term442 r i n)). Qed.
Lemma lem1298292 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : (term442 r i n) = True.
Proof. exact (EQ_MP (@lem1298287 r i n) (@lem1298286 i n r h1)). Qed.
Lemma lem1298293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298294 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : (term636 r i n) = (and True).
Proof. exact (MK_COMB (@lem1298293) (@lem1298292 i n r h1)). Qed.
Lemma lem1298298 (m : nat) (n : nat) (p : nat) : (term91 m n p) = (term92 m n p).
Proof. exact (EQ_MP (@lem1298259 m n p) (@lem1298258 m n p)). Qed.
Lemma lem1298299 (r : nat -> nat) (n : nat) (i : nat) : (term547 r n i) = (term637 r n i).
Proof. exact (@lem1298298 (term444 n r i) n i). Qed.
Lemma lem1298300 (r : nat -> nat) (i : nat) (n : nat) : (term638 r i n) = (term638 r i n).
Proof. exact (eq_refl (term638 r i n)). Qed.
Lemma lem1298301 (r : nat -> nat) (n : nat) (i : nat) : (term639 r n i) = (term640 r n i).
Proof. exact (MK_COMB (@lem1298300 r i n) (@lem1298299 r n i)). Qed.
Lemma lem1298303 (m : nat) (n : nat) : (term633 m n) = True.
Proof. exact (EQ_MP (@lem1298250 m n) (@lem1298249 m n)). Qed.
Lemma lem1298304 (r : nat -> nat) (n : nat) (i : nat) : (term640 r n i) = True.
Proof. exact (@lem1298303 (term445 r i n) i). Qed.
Lemma lem1298305 (r : nat -> nat) (n : nat) (i : nat) : (term639 r n i) = True.
Proof. exact (TRANS (@lem1298301 r n i) (@lem1298304 r n i)). Qed.
Lemma lem1298306 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : (term641 r n i) = (True /\ True).
Proof. exact (MK_COMB (@lem1298294 i n r h1) (@lem1298305 r n i)). Qed.
Lemma lem1298308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1298309 : (True /\ True) = True.
Proof. exact (@lem1298308 True). Qed.
Lemma lem1298310 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : (term641 r n i) = True.
Proof. exact (TRANS (@lem1298306 n i r h1) (@lem1298309)). Qed.
Lemma lem1298311 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : True = (term641 r n i).
Proof. exact (SYM (@lem1298310 n i r h1)). Qed.
Lemma lem1298312 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term641 r n i.
Proof. exact (EQ_MP (@lem1298311 n i r h1) (@lem0)). Qed.
Lemma lem1298313 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term642 r n i.
Proof. exact (ex_intro (term643 r n i) (term445 r i n) (@lem1298312 n i r h1)). Qed.
Lemma lem1298314 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term549 r n i.
Proof. exact (@lem1298243 r n i (@lem1298313 n i r h1)). Qed.
Lemma lem1298319 (i : nat) (r : nat -> nat) (h1 : term438 r) : term619 r i.
Proof. exact (fun n : nat => @lem1298314 n i r h1). Qed.
Lemma lem1298324 (r : nat -> nat) (h1 : term438 r) : term622 r.
Proof. exact (fun i : nat => @lem1298319 i r h1). Qed.
Lemma lem1298325 (r : nat -> nat) (h1 : term438 r) : term625 r.
Proof. exact (EQ_MP (@lem1298240 r) (@lem1298324 r h1)). Qed.
Lemma lem1298326 (r : nat -> nat) (h1 : term438 r) : term623 r.
Proof. exact (EQ_MP (@lem1298214 r) (@lem1298325 r h1)). Qed.
Lemma lem1298327 (r : nat -> nat) (h1 : term438 r) : term603 r.
Proof. exact (EQ_MP (@lem1298197 r) (@lem1298326 r h1)). Qed.
Lemma lem1298328 (r : nat -> nat) (h1 : term438 r) : term559 r.
Proof. exact (EQ_MP (@lem1298164 r) (@lem1298327 r h1)). Qed.
Lemma lem1298329 (r : nat -> nat) (h1 : term438 r) : term558 r.
Proof. exact (EQ_MP (@lem1298073 r) (@lem1298328 r h1)). Qed.
Lemma lem1298330 (r : nat -> nat) (h1 : term438 r) : term536 r.
Proof. exact (ex_intro (term535 r) term644 (@lem1298329 r h1)). Qed.
Lemma lem1298331 (r : nat -> nat) (h1 : term438 r) : is_nadd r.
Proof. exact (EQ_MP (@lem1298029 r) (@lem1298330 r h1)). Qed.
Lemma lem1298332 (r : nat -> nat) (h1 : term438 r) : (term145 r) = r.
Proof. exact (EQ_MP (@lem1297986 r) (@lem1298331 r h1)). Qed.
Lemma lem1298333 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1298335 (x : nadd) (y : nadd) : term60 x y.
Proof. exact (EQ_MP (@lem1296476 x y) (@lem1296475 x y)). Qed.
Lemma lem1298336 (x : nadd) (r : nat -> nat) : term645 x r.
Proof. exact (@lem1298335 x (mk_nadd r)). Qed.
Lemma lem1298338 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296448 x z) (@lem1296447 x z)). Qed.
Lemma lem1298339 (x : nadd) (n : nat) (r : nat -> nat) : term646 x n r.
Proof. exact (@lem1298338 (term247 n x) (term647 n r)). Qed.
Lemma lem1298340 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term437 P r.
Proof. exact (h1). Qed.
Lemma lem1298341 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term491 P r n.
Proof. exact (@lem1298340 P r h1 n). Qed.
Lemma lem1298342 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term491 P r n) = (term436 P r n).
Proof. exact (eq_refl (term491 P r n)). Qed.
Lemma lem1298343 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term436 P r n.
Proof. exact (EQ_MP (@lem1298342 P r n) (@lem1298341 n P r h1)). Qed.
Lemma lem1298344 (n : nat) (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term492 P r n x.
Proof. exact (@lem1298343 n P r h1 x). Qed.
Lemma lem1298345 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (n : nat) : (term492 P r n x) = (term435 P x r n).
Proof. exact (eq_refl (term492 P r n x)). Qed.
Lemma lem1298346 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term435 P x r n.
Proof. exact (EQ_MP (@lem1298345 P x r n) (@lem1298344 n x P r h1)). Qed.
Lemma lem1298347 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1298348 (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term437 P r) (h2 : P x) : term434 x r n.
Proof. exact (@lem1298346 x n P r h1 (@lem1298347 P x h2)). Qed.
Lemma lem1298349 (r : nat -> nat) (n : nat) (P : nadd -> Prop) (x : nadd) (h1 : P x) : term493 P x r n.
Proof. exact (fun h0 : term437 P r => @lem1298348 n r P x h0 h1). Qed.
Lemma lem1298350 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term437 P r.
Proof. exact (h1). Qed.
Lemma lem1298351 (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term437 P r) (h2 : P x) : term434 x r n.
Proof. exact (@lem1298349 r n P x h2 (@lem1298350 P r h1)). Qed.
Lemma lem1298352 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term435 P x r n.
Proof. exact (fun h0 : P x => @lem1298351 n r P x h1 h0). Qed.
Lemma lem1298353 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term494 P x r.
Proof. exact (fun n : nat => @lem1298352 x n P r h1). Qed.
Lemma lem1298354 (P : nadd -> Prop) (r : nat -> nat) (h1 : term437 P r) : term495 P r.
Proof. exact (fun x : nadd => @lem1298353 x P r h1). Qed.
Lemma lem1298355 (P : nadd -> Prop) (r : nat -> nat) : term496 P r.
Proof. exact (fun h0 : term437 P r => @lem1298354 P r h0). Qed.
Lemma lem1298356 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term495 P r.
Proof. exact (@lem1298355 P r (@lem1297726 P r h1)). Qed.
Lemma lem1298357 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term497 P r x.
Proof. exact (@lem1298356 P r h1 x). Qed.
Lemma lem1298358 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) : (term497 P r x) = (term494 P x r).
Proof. exact (eq_refl (term497 P r x)). Qed.
Lemma lem1298359 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term494 P x r.
Proof. exact (EQ_MP (@lem1298358 P x r) (@lem1298357 x P r h1)). Qed.
Lemma lem1298360 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term498 P x r n.
Proof. exact (@lem1298359 x P r h1 n). Qed.
Lemma lem1298361 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (n : nat) : (term498 P x r n) = (term435 P x r n).
Proof. exact (eq_refl (term498 P x r n)). Qed.
Lemma lem1298364 (x : nadd) (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term435 P x r n.
Proof. exact (EQ_MP (@lem1298361 P x r n) (@lem1298360 x n P r h1)). Qed.
Lemma lem1298393 (P : nadd -> Prop) (x : nadd) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1298396 (P : nadd -> Prop) (x : nadd) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1298393 P x) (@lem1298333 P x h1)). Qed.
Lemma lem1298397 (P : nadd -> Prop) (x : nadd) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1298396 P x h1)). Qed.
Lemma lem1298398 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1298397 P x h1) (@lem0)). Qed.
Lemma lem1298399 (n : nat) (r : nat -> nat) (P : nadd -> Prop) (x : nadd) (h1 : term422 P r) (h2 : P x) : term434 x r n.
Proof. exact (@lem1298364 x n P r h1 (@lem1298398 P x h2)). Qed.
Lemma lem1298400 (k : nat) : term648 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1298401 (k : nat) : (term648 k) = ((term649 k) = (term650 k)).
Proof. exact (eq_refl (term648 k)). Qed.
Lemma lem1298403 (x : nadd) : term651 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1298404 (x : nadd) : (term651 x) = (term652 x).
Proof. exact (eq_refl (term651 x)). Qed.
Lemma lem1298405 (x : nadd) : term652 x.
Proof. exact (EQ_MP (@lem1298404 x) (@lem1298403 x)). Qed.
Lemma lem1298406 (x : nadd) (y : nadd) : term653 x y.
Proof. exact (@lem1298405 x y). Qed.
Lemma lem1298407 (x : nadd) (y : nadd) : (term653 x y) = ((term654 x y) = (term655 x y)).
Proof. exact (eq_refl (term653 x y)). Qed.
Lemma lem1298409 (x : nadd) : term656 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1298410 (x : nadd) : (term656 x) = (term657 x).
Proof. exact (eq_refl (term656 x)). Qed.
Lemma lem1298411 (x : nadd) : term657 x.
Proof. exact (EQ_MP (@lem1298410 x) (@lem1298409 x)). Qed.
Lemma lem1298412 (x : nadd) (y : nadd) : term658 x y.
Proof. exact (@lem1298411 x y). Qed.
Lemma lem1298413 (x : nadd) (y : nadd) : (term658 x y) = ((term659 x y) = (term660 x y)).
Proof. exact (eq_refl (term658 x y)). Qed.
Lemma lem1298415 (x : nadd) : term661 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1298416 (x : nadd) : (term661 x) = (term662 x).
Proof. exact (eq_refl (term661 x)). Qed.
Lemma lem1298417 (x : nadd) : term662 x.
Proof. exact (EQ_MP (@lem1298416 x) (@lem1298415 x)). Qed.
Lemma lem1298418 (x : nadd) (y : nadd) : term663 x y.
Proof. exact (@lem1298417 x y). Qed.
Lemma lem1298419 (x : nadd) (y : nadd) : (term663 x y) = ((nadd_le x y) = (term664 x y)).
Proof. exact (eq_refl (term663 x y)). Qed.
Lemma lem1298452 (x : nadd) (y : nadd) : (nadd_le x y) = (term664 x y).
Proof. exact (EQ_MP (@lem1298419 x y) (@lem1298418 x y)). Qed.
Lemma lem1298453 (n : nat) (r : nat -> nat) : (term665 n r) = (term666 n r).
Proof. exact (@lem1298452 (term250 r n) (term647 n r)). Qed.
Lemma lem1298463 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298401 k) (@lem1298400 k)). Qed.
Lemma lem1298464 (r : nat -> nat) (n : nat) : (term667 r n) = (term668 r n).
Proof. exact (@lem1298463 (term395 r n)). Qed.
Lemma lem1298465 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298466 (r : nat -> nat) (n : nat) (n' : nat) : (term669 r n n') = (term670 r n n').
Proof. exact (MK_COMB (@lem1298464 r n) (@lem1298465 n')). Qed.
Lemma lem1298468 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1298469 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1298468 nat nat f y). Qed.
Lemma lem1298470 (r : nat -> nat) (n : nat) (n' : nat) : (term673 r n n') = (term670 r n n').
Proof. exact (@lem1298469 (term668 r n) n'). Qed.
Lemma lem1298471 (r : nat -> nat) (n : nat) (n' : nat) : (term670 r n n') = (term674 r n n').
Proof. exact (eq_refl (term670 r n n')). Qed.
Lemma lem1298472 (r : nat -> nat) (n : nat) : (term675 r n) = (term668 r n).
Proof. exact (fun_ext (fun n' : nat => @lem1298471 r n n')). Qed.
Lemma lem1298473 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298474 (r : nat -> nat) (n : nat) (n' : nat) : (term673 r n n') = (term670 r n n').
Proof. exact (MK_COMB (@lem1298472 r n) (@lem1298473 n')). Qed.
Lemma lem1298475 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1298476 (r : nat -> nat) (n : nat) (n' : nat) : (term676 r n n') = (term677 r n n').
Proof. exact (MK_COMB (@lem1298475) (@lem1298474 r n n')). Qed.
Lemma lem1298477 (r : nat -> nat) (n : nat) (n' : nat) : (term670 r n n') = (term674 r n n').
Proof. exact (eq_refl (term670 r n n')). Qed.
Lemma lem1298478 (r : nat -> nat) (n : nat) (n' : nat) : ((term673 r n n') = (term670 r n n')) = ((term670 r n n') = (term674 r n n')).
Proof. exact (MK_COMB (@lem1298476 r n n') (@lem1298477 r n n')). Qed.
Lemma lem1298479 (r : nat -> nat) (n : nat) (n' : nat) : (term670 r n n') = (term674 r n n').
Proof. exact (EQ_MP (@lem1298478 r n n') (@lem1298470 r n n')). Qed.
Lemma lem1298480 (r : nat -> nat) (n : nat) (n' : nat) : (term669 r n n') = (term674 r n n').
Proof. exact (TRANS (@lem1298466 r n n') (@lem1298479 r n n')). Qed.
Lemma lem1298481 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298482 (r : nat -> nat) (n : nat) (n' : nat) : (term678 r n n') = (term679 r n n').
Proof. exact (MK_COMB (@lem1298481) (@lem1298480 r n n')). Qed.
Lemma lem1298484 (x : nadd) (y : nadd) : (term659 x y) = (term660 x y).
Proof. exact (EQ_MP (@lem1298413 x y) (@lem1298412 x y)). Qed.
Lemma lem1298485 (n : nat) (r : nat -> nat) : (term680 n r) = (term681 n r).
Proof. exact (@lem1298484 (term682 n r) term683). Qed.
Lemma lem1298487 (x : nadd) (y : nadd) : (term654 x y) = (term655 x y).
Proof. exact (EQ_MP (@lem1298407 x y) (@lem1298406 x y)). Qed.
Lemma lem1298488 (n : nat) (r : nat -> nat) : (term684 n r) = (term685 n r).
Proof. exact (@lem1298487 (nadd_of_num n) (mk_nadd r)). Qed.
Lemma lem1298490 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298401 k) (@lem1298400 k)). Qed.
Lemma lem1298491 (n : nat) : (term649 n) = (term650 n).
Proof. exact (@lem1298490 n). Qed.
Lemma lem1298493 (r : nat -> nat) (h1 : (term145 r) = r) : (term145 r) = r.
Proof. exact (h1). Qed.
Lemma lem1298494 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298495 (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term686 r n') = (r n').
Proof. exact (MK_COMB (@lem1298493 r h1) (@lem1298494 n')). Qed.
Lemma lem1298496 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term687 n r n') = (term688 n r n').
Proof. exact (MK_COMB (@lem1298491 n) (@lem1298495 n' r h1)). Qed.
Lemma lem1298498 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1298499 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1298498 nat nat f y). Qed.
Lemma lem1298500 (n : nat) (r : nat -> nat) (n' : nat) : (term689 n r n') = (term688 n r n').
Proof. exact (@lem1298499 (term650 n) (r n')). Qed.
Lemma lem1298501 (n : nat) (n' : nat) : (term690 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term690 n n')). Qed.
Lemma lem1298502 (n : nat) : (term691 n) = (term650 n).
Proof. exact (fun_ext (fun n' : nat => @lem1298501 n n')). Qed.
Lemma lem1298503 (r : nat -> nat) (n' : nat) : (r n') = (r n').
Proof. exact (eq_refl (r n')). Qed.
Lemma lem1298504 (n : nat) (r : nat -> nat) (n' : nat) : (term689 n r n') = (term688 n r n').
Proof. exact (MK_COMB (@lem1298502 n) (@lem1298503 r n')). Qed.
Lemma lem1298505 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1298506 (n : nat) (r : nat -> nat) (n' : nat) : (term692 n r n') = (term693 n r n').
Proof. exact (MK_COMB (@lem1298505) (@lem1298504 n r n')). Qed.
Lemma lem1298507 (n : nat) (r : nat -> nat) (n' : nat) : (term688 n r n') = (term444 n r n').
Proof. exact (eq_refl (term688 n r n')). Qed.
Lemma lem1298508 (n : nat) (r : nat -> nat) (n' : nat) : ((term689 n r n') = (term688 n r n')) = ((term688 n r n') = (term444 n r n')).
Proof. exact (MK_COMB (@lem1298506 n r n') (@lem1298507 n r n')). Qed.
Lemma lem1298509 (n : nat) (r : nat -> nat) (n' : nat) : (term688 n r n') = (term444 n r n').
Proof. exact (EQ_MP (@lem1298508 n r n') (@lem1298500 n r n')). Qed.
Lemma lem1298510 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term687 n r n') = (term444 n r n').
Proof. exact (TRANS (@lem1298496 n n' r h1) (@lem1298509 n r n')). Qed.
Lemma lem1298511 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term685 n r) = (term694 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298510 n n' r h1)). Qed.
Lemma lem1298512 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term684 n r) = (term694 n r).
Proof. exact (TRANS (@lem1298488 n r) (@lem1298511 n r h1)). Qed.
Lemma lem1298513 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298514 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term695 n r n') = (term696 n r n').
Proof. exact (MK_COMB (@lem1298512 n r h1) (@lem1298513 n')). Qed.
Lemma lem1298516 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1298517 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1298516 nat nat f y). Qed.
Lemma lem1298518 (n : nat) (r : nat -> nat) (n' : nat) : (term697 n r n') = (term696 n r n').
Proof. exact (@lem1298517 (term694 n r) n'). Qed.
Lemma lem1298519 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (eq_refl (term696 n r n')). Qed.
Lemma lem1298520 (n : nat) (r : nat -> nat) : (term698 n r) = (term694 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298519 n r n')). Qed.
Lemma lem1298521 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298522 (n : nat) (r : nat -> nat) (n' : nat) : (term697 n r n') = (term696 n r n').
Proof. exact (MK_COMB (@lem1298520 n r) (@lem1298521 n')). Qed.
Lemma lem1298523 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1298524 (n : nat) (r : nat -> nat) (n' : nat) : (term699 n r n') = (term700 n r n').
Proof. exact (MK_COMB (@lem1298523) (@lem1298522 n r n')). Qed.
Lemma lem1298525 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (eq_refl (term696 n r n')). Qed.
Lemma lem1298526 (n : nat) (r : nat -> nat) (n' : nat) : ((term697 n r n') = (term696 n r n')) = ((term696 n r n') = (term444 n r n')).
Proof. exact (MK_COMB (@lem1298524 n r n') (@lem1298525 n r n')). Qed.
Lemma lem1298527 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (EQ_MP (@lem1298526 n r n') (@lem1298518 n r n')). Qed.
Lemma lem1298528 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term695 n r n') = (term444 n r n').
Proof. exact (TRANS (@lem1298514 n n' r h1) (@lem1298527 n r n')). Qed.
Lemma lem1298529 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1298530 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term701 n r n') = (term538 n r n').
Proof. exact (MK_COMB (@lem1298529) (@lem1298528 n n' r h1)). Qed.
Lemma lem1298532 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298401 k) (@lem1298400 k)). Qed.
Lemma lem1298533 : term702 = term703.
Proof. exact (@lem1298532 term704). Qed.
Lemma lem1298534 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298535 (n' : nat) : (term705 n') = (term706 n').
Proof. exact (MK_COMB (@lem1298533) (@lem1298534 n')). Qed.
Lemma lem1298537 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1298538 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1298537 nat nat f y). Qed.
Lemma lem1298539 (n' : nat) : (term707 n') = (term706 n').
Proof. exact (@lem1298538 term703 n'). Qed.
Lemma lem1298540 (n : nat) : (term706 n) = (term118 n).
Proof. exact (eq_refl (term706 n)). Qed.
Lemma lem1298541 : term708 = term703.
Proof. exact (fun_ext (fun n : nat => @lem1298540 n)). Qed.
Lemma lem1298542 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298543 (n' : nat) : (term707 n') = (term706 n').
Proof. exact (MK_COMB (@lem1298541) (@lem1298542 n')). Qed.
Lemma lem1298544 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1298545 (n' : nat) : (term709 n') = (term710 n').
Proof. exact (MK_COMB (@lem1298544) (@lem1298543 n')). Qed.
Lemma lem1298546 (n' : nat) : (term706 n') = (term118 n').
Proof. exact (eq_refl (term706 n')). Qed.
Lemma lem1298547 (n' : nat) : ((term707 n') = (term706 n')) = ((term706 n') = (term118 n')).
Proof. exact (MK_COMB (@lem1298545 n') (@lem1298546 n')). Qed.
Lemma lem1298548 (n' : nat) : (term706 n') = (term118 n').
Proof. exact (EQ_MP (@lem1298547 n') (@lem1298539 n')). Qed.
Lemma lem1298549 (n' : nat) : (term705 n') = (term118 n').
Proof. exact (TRANS (@lem1298535 n') (@lem1298548 n')). Qed.
Lemma lem1298550 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term711 n r n') = (term712 n r n').
Proof. exact (MK_COMB (@lem1298530 n n' r h1) (@lem1298549 n')). Qed.
Lemma lem1298551 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term681 n r) = (term713 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298550 n n' r h1)). Qed.
Lemma lem1298552 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term680 n r) = (term713 n r).
Proof. exact (TRANS (@lem1298485 n r) (@lem1298551 n r h1)). Qed.
Lemma lem1298553 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298554 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term714 n r n') = (term715 n r n').
Proof. exact (MK_COMB (@lem1298552 n r h1) (@lem1298553 n')). Qed.
Lemma lem1298556 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1298557 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1298556 nat nat f y). Qed.
Lemma lem1298558 (n : nat) (r : nat -> nat) (n' : nat) : (term716 n r n') = (term715 n r n').
Proof. exact (@lem1298557 (term713 n r) n'). Qed.
Lemma lem1298559 (n : nat) (r : nat -> nat) (n' : nat) : (term715 n r n') = (term712 n r n').
Proof. exact (eq_refl (term715 n r n')). Qed.
Lemma lem1298560 (n : nat) (r : nat -> nat) : (term717 n r) = (term713 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298559 n r n')). Qed.
Lemma lem1298561 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298562 (n : nat) (r : nat -> nat) (n' : nat) : (term716 n r n') = (term715 n r n').
Proof. exact (MK_COMB (@lem1298560 n r) (@lem1298561 n')). Qed.
Lemma lem1298563 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1298564 (n : nat) (r : nat -> nat) (n' : nat) : (term718 n r n') = (term719 n r n').
Proof. exact (MK_COMB (@lem1298563) (@lem1298562 n r n')). Qed.
Lemma lem1298565 (n : nat) (r : nat -> nat) (n' : nat) : (term715 n r n') = (term712 n r n').
Proof. exact (eq_refl (term715 n r n')). Qed.
Lemma lem1298566 (n : nat) (r : nat -> nat) (n' : nat) : ((term716 n r n') = (term715 n r n')) = ((term715 n r n') = (term712 n r n')).
Proof. exact (MK_COMB (@lem1298564 n r n') (@lem1298565 n r n')). Qed.
Lemma lem1298567 (n : nat) (r : nat -> nat) (n' : nat) : (term715 n r n') = (term712 n r n').
Proof. exact (EQ_MP (@lem1298566 n r n') (@lem1298558 n r n')). Qed.
Lemma lem1298568 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term714 n r n') = (term712 n r n').
Proof. exact (TRANS (@lem1298554 n n' r h1) (@lem1298567 n r n')). Qed.
Lemma lem1298569 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1298570 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term720 n r n') = (term721 n r n').
Proof. exact (MK_COMB (@lem1298569) (@lem1298568 n n' r h1)). Qed.
Lemma lem1298571 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1298572 (n : nat) (n' : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term722 n r n' B) = (term723 n r n' B).
Proof. exact (MK_COMB (@lem1298570 n n' r h1) (@lem1298571 B)). Qed.
Lemma lem1298573 (n : nat) (n' : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term724 n r n' B) = (term725 n r n' B).
Proof. exact (MK_COMB (@lem1298482 r n n') (@lem1298572 n n' B r h1)). Qed.
Lemma lem1298574 (n : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term726 n r B) = (term727 n r B).
Proof. exact (fun_ext (fun n' : nat => @lem1298573 n n' B r h1)). Qed.
Lemma lem1298575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298576 (n : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term728 n r B) = (term729 n r B).
Proof. exact (MK_COMB (@lem1298575) (@lem1298574 n B r h1)). Qed.
Lemma lem1298581 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term730 n r) = (term731 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298576 n B r h1)). Qed.
Lemma lem1298582 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298583 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term666 n r) = (term732 n r).
Proof. exact (MK_COMB (@lem1298582) (@lem1298581 n r h1)). Qed.
Lemma lem1298588 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term665 n r) = (term732 n r).
Proof. exact (TRANS (@lem1298453 n r) (@lem1298583 n r h1)). Qed.
Lemma lem1298589 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term732 n r) = (term665 n r).
Proof. exact (SYM (@lem1298588 n r h1)). Qed.
Lemma lem1298599 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1296420 n m) (@lem1296419 m n)). Qed.
Lemma lem1298600 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term723 n r n' B) = (term733 B n r n').
Proof. exact (@lem1298599 B (term712 n r n')). Qed.
Lemma lem1298601 (r : nat -> nat) (n : nat) (n' : nat) : (term679 r n n') = (term679 r n n').
Proof. exact (eq_refl (term679 r n n')). Qed.
Lemma lem1298602 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term725 n r n' B) = (term734 B n r n').
Proof. exact (MK_COMB (@lem1298601 r n n') (@lem1298600 B n r n')). Qed.
Lemma lem1298603 (B : nat) (n : nat) (r : nat -> nat) : (term727 n r B) = (term735 B n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298602 B n r n')). Qed.
Lemma lem1298604 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298605 (B : nat) (n : nat) (r : nat -> nat) : (term729 n r B) = (term736 B n r).
Proof. exact (MK_COMB (@lem1298604) (@lem1298603 B n r)). Qed.
Lemma lem1298606 (n : nat) (r : nat -> nat) : (term731 n r) = (term737 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298605 B n r)). Qed.
Lemma lem1298607 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298608 (n : nat) (r : nat -> nat) : (term732 n r) = (term738 n r).
Proof. exact (MK_COMB (@lem1298607) (@lem1298606 n r)). Qed.
Lemma lem1298609 (n : nat) (r : nat -> nat) : (term738 n r) = (term732 n r).
Proof. exact (SYM (@lem1298608 n r)). Qed.
Lemma lem1298619 (m : nat) : (S m) = (term127 m).
Proof. exact (EQ_MP (@lem1296414 m) (@lem1296413 m)). Qed.
Lemma lem1298620 (r : nat -> nat) (n : nat) : (term395 r n) = (term739 r n).
Proof. exact (@lem1298619 (r n)). Qed.
Lemma lem1298621 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1298622 (r : nat -> nat) (n : nat) : (term740 r n) = (term741 r n).
Proof. exact (MK_COMB (@lem1298621) (@lem1298620 r n)). Qed.
Lemma lem1298623 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1298624 (r : nat -> nat) (n : nat) (n' : nat) : (term674 r n n') = (term742 r n n').
Proof. exact (MK_COMB (@lem1298622 r n) (@lem1298623 n')). Qed.
Lemma lem1298626 (m : nat) (n : nat) (p : nat) : (term124 m n p) = (term125 m n p).
Proof. exact (EQ_MP (@lem1296411 m n p) (@lem1296410 m n p)). Qed.
Lemma lem1298627 (r : nat -> nat) (n : nat) (n' : nat) : (term742 r n n') = (term743 r n n').
Proof. exact (@lem1298626 (r n) term644 n'). Qed.
Lemma lem1298628 (r : nat -> nat) (n : nat) (n' : nat) : (term674 r n n') = (term743 r n n').
Proof. exact (TRANS (@lem1298624 r n n') (@lem1298627 r n n')). Qed.
Lemma lem1298629 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298630 (r : nat -> nat) (n : nat) (n' : nat) : (term679 r n n') = (term744 r n n').
Proof. exact (MK_COMB (@lem1298629) (@lem1298628 r n n')). Qed.
Lemma lem1298631 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term733 B n r n') = (term733 B n r n').
Proof. exact (eq_refl (term733 B n r n')). Qed.
Lemma lem1298632 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term734 B n r n') = (term745 B n r n').
Proof. exact (MK_COMB (@lem1298630 r n n') (@lem1298631 B n r n')). Qed.
Lemma lem1298633 (B : nat) (n : nat) (r : nat -> nat) : (term735 B n r) = (term746 B n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298632 B n r n')). Qed.
Lemma lem1298634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298635 (B : nat) (n : nat) (r : nat -> nat) : (term736 B n r) = (term747 B n r).
Proof. exact (MK_COMB (@lem1298634) (@lem1298633 B n r)). Qed.
Lemma lem1298640 (n : nat) (r : nat -> nat) : (term737 n r) = (term748 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298635 B n r)). Qed.
Lemma lem1298641 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298642 (n : nat) (r : nat -> nat) : (term738 n r) = (term749 n r).
Proof. exact (MK_COMB (@lem1298641) (@lem1298640 n r)). Qed.
Lemma lem1298647 (n : nat) (r : nat -> nat) : (term749 n r) = (term738 n r).
Proof. exact (SYM (@lem1298642 n r)). Qed.
Lemma lem1298659 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem1296391 n) (@lem1296390 n)). Qed.
Lemma lem1298660 (n' : nat) : (term44 n') = n'.
Proof. exact (@lem1298659 n'). Qed.
Lemma lem1298661 (r : nat -> nat) (n : nat) (n' : nat) : (term750 r n n') = (term750 r n n').
Proof. exact (eq_refl (term750 r n n')). Qed.
Lemma lem1298662 (r : nat -> nat) (n : nat) (n' : nat) : (term743 r n n') = (term751 r n n').
Proof. exact (MK_COMB (@lem1298661 r n n') (@lem1298660 n')). Qed.
Lemma lem1298663 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298664 (r : nat -> nat) (n : nat) (n' : nat) : (term744 r n n') = (term752 r n n').
Proof. exact (MK_COMB (@lem1298663) (@lem1298662 r n n')). Qed.
Lemma lem1298666 (m : nat) (n : nat) (p : nat) : (term91 m n p) = (term92 m n p).
Proof. exact (EQ_MP (@lem1296365 m n p) (@lem1296364 m n p)). Qed.
Lemma lem1298667 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term733 B n r n') = (term753 B n r n').
Proof. exact (@lem1298666 B (term444 n r n') (term118 n')). Qed.
Lemma lem1298669 (n : nat) : (term118 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem1296402 n) (@lem1296401 n)). Qed.
Lemma lem1298670 (n' : nat) : (term118 n') = (Nat.add n' n').
Proof. exact (@lem1298669 n'). Qed.
Lemma lem1298671 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term754 B n r n') = (term754 B n r n').
Proof. exact (eq_refl (term754 B n r n')). Qed.
Lemma lem1298672 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term753 B n r n') = (term755 B n r n').
Proof. exact (MK_COMB (@lem1298671 B n r n') (@lem1298670 n')). Qed.
Lemma lem1298674 (m : nat) (n : nat) (p : nat) : (term91 m n p) = (term92 m n p).
Proof. exact (EQ_MP (@lem1296365 m n p) (@lem1296364 m n p)). Qed.
Lemma lem1298675 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term755 B n r n') = (term756 B n r n').
Proof. exact (@lem1298674 (term757 B n r n') n' n'). Qed.
Lemma lem1298676 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term753 B n r n') = (term756 B n r n').
Proof. exact (TRANS (@lem1298672 B n r n') (@lem1298675 B n r n')). Qed.
Lemma lem1298677 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term733 B n r n') = (term756 B n r n').
Proof. exact (TRANS (@lem1298667 B n r n') (@lem1298676 B n r n')). Qed.
Lemma lem1298678 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term745 B n r n') = (term758 B n r n').
Proof. exact (MK_COMB (@lem1298664 r n n') (@lem1298677 B n r n')). Qed.
Lemma lem1298680 (p : nat) (m : nat) (n : nat) : (term113 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1296356 p m n) (@lem1296355 m n p)). Qed.
Lemma lem1298681 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term758 B n r n') = (term759 B n r n').
Proof. exact (@lem1298680 n' (term760 r n n') (term761 B n r n')). Qed.
Lemma lem1298682 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term745 B n r n') = (term759 B n r n').
Proof. exact (TRANS (@lem1298678 B n r n') (@lem1298681 B n r n')). Qed.
Lemma lem1298683 (B : nat) (n : nat) (r : nat -> nat) : (term746 B n r) = (term762 B n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298682 B n r n')). Qed.
Lemma lem1298684 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298685 (B : nat) (n : nat) (r : nat -> nat) : (term747 B n r) = (term763 B n r).
Proof. exact (MK_COMB (@lem1298684) (@lem1298683 B n r)). Qed.
Lemma lem1298690 (n : nat) (r : nat -> nat) : (term748 n r) = (term764 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298685 B n r)). Qed.
Lemma lem1298691 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298692 (n : nat) (r : nat -> nat) : (term749 n r) = (term765 n r).
Proof. exact (MK_COMB (@lem1298691) (@lem1298690 n r)). Qed.
Lemma lem1298697 (n : nat) (r : nat -> nat) : (term765 n r) = (term749 n r).
Proof. exact (SYM (@lem1298692 n r)). Qed.
Lemma lem1298707 (m : nat) (n : nat) (p : nat) : (term92 m n p) = (term91 m n p).
Proof. exact (EQ_MP (@lem1296347 m n p) (@lem1296346 m n p)). Qed.
Lemma lem1298708 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term761 B n r n') = (term766 B n r n').
Proof. exact (@lem1298707 B (term444 n r n') n'). Qed.
Lemma lem1298709 (r : nat -> nat) (n : nat) (n' : nat) : (term767 r n n') = (term767 r n n').
Proof. exact (eq_refl (term767 r n n')). Qed.
Lemma lem1298710 (B : nat) (n : nat) (r : nat -> nat) (n' : nat) : (term759 B n r n') = (term768 B n r n').
Proof. exact (MK_COMB (@lem1298709 r n n') (@lem1298708 B n r n')). Qed.
Lemma lem1298711 (B : nat) (n : nat) (r : nat -> nat) : (term762 B n r) = (term769 B n r).
Proof. exact (fun_ext (fun n' : nat => @lem1298710 B n r n')). Qed.
Lemma lem1298712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298713 (B : nat) (n : nat) (r : nat -> nat) : (term763 B n r) = (term770 B n r).
Proof. exact (MK_COMB (@lem1298712) (@lem1298711 B n r)). Qed.
Lemma lem1298718 (n : nat) (r : nat -> nat) : (term764 n r) = (term771 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298713 B n r)). Qed.
Lemma lem1298719 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298720 (n : nat) (r : nat -> nat) : (term765 n r) = (term772 n r).
Proof. exact (MK_COMB (@lem1298719) (@lem1298718 n r)). Qed.
Lemma lem1298725 (n : nat) (r : nat -> nat) : (term772 n r) = (term765 n r).
Proof. exact (SYM (@lem1298720 n r)). Qed.
Lemma lem1298735 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1296320 n m) (@lem1296319 m n)). Qed.
Lemma lem1298736 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term766 B n r n') = (term773 n r n' B).
Proof. exact (@lem1298735 (term774 n r n') B). Qed.
Lemma lem1298737 (r : nat -> nat) (n : nat) (n' : nat) : (term767 r n n') = (term767 r n n').
Proof. exact (eq_refl (term767 r n n')). Qed.
Lemma lem1298738 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term768 B n r n') = (term775 n r n' B).
Proof. exact (MK_COMB (@lem1298737 r n n') (@lem1298736 n r n' B)). Qed.
Lemma lem1298739 (n : nat) (r : nat -> nat) (B : nat) : (term769 B n r) = (term776 n r B).
Proof. exact (fun_ext (fun n' : nat => @lem1298738 n r n' B)). Qed.
Lemma lem1298740 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298741 (n : nat) (r : nat -> nat) (B : nat) : (term770 B n r) = (term777 n r B).
Proof. exact (MK_COMB (@lem1298740) (@lem1298739 n r B)). Qed.
Lemma lem1298742 (n : nat) (r : nat -> nat) : (term771 n r) = (term778 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298741 n r B)). Qed.
Lemma lem1298743 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298744 (n : nat) (r : nat -> nat) : (term772 n r) = (term779 n r).
Proof. exact (MK_COMB (@lem1298743) (@lem1298742 n r)). Qed.
Lemma lem1298745 (n : nat) (r : nat -> nat) : (term779 n r) = (term772 n r).
Proof. exact (SYM (@lem1298744 n r)). Qed.
Lemma lem1298747 (P : nat -> nat) (Q : nat -> nat) : (term86 P Q) = (term87 P Q).
Proof. exact (EQ_MP (@lem1296314 P Q) (@lem1296313 P Q)). Qed.
Lemma lem1298748 (n : nat) (r : nat -> nat) : (term780 n r) = (term781 n r).
Proof. exact (@lem1298747 (term782 r n) (term783 n r)). Qed.
Lemma lem1298749 (r : nat -> nat) (n : nat) (n' : nat) : (term784 r n n') = (term760 r n n').
Proof. exact (eq_refl (term784 r n n')). Qed.
Lemma lem1298750 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298751 (r : nat -> nat) (n : nat) (n' : nat) : (term785 r n n') = (term767 r n n').
Proof. exact (MK_COMB (@lem1298750) (@lem1298749 r n n')). Qed.
Lemma lem1298752 (n : nat) (r : nat -> nat) (n' : nat) : (term786 n r n') = (term774 n r n').
Proof. exact (eq_refl (term786 n r n')). Qed.
Lemma lem1298753 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1298754 (n : nat) (r : nat -> nat) (n' : nat) : (term787 n r n') = (term788 n r n').
Proof. exact (MK_COMB (@lem1298753) (@lem1298752 n r n')). Qed.
Lemma lem1298755 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1298756 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term789 n r n' B) = (term773 n r n' B).
Proof. exact (MK_COMB (@lem1298754 n r n') (@lem1298755 B)). Qed.
Lemma lem1298757 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term790 n r n' B) = (term775 n r n' B).
Proof. exact (MK_COMB (@lem1298751 r n n') (@lem1298756 n r n' B)). Qed.
Lemma lem1298758 (n : nat) (r : nat -> nat) (B : nat) : (term791 n r B) = (term776 n r B).
Proof. exact (fun_ext (fun n' : nat => @lem1298757 n r n' B)). Qed.
Lemma lem1298759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298760 (n : nat) (r : nat -> nat) (B : nat) : (term792 n r B) = (term777 n r B).
Proof. exact (MK_COMB (@lem1298759) (@lem1298758 n r B)). Qed.
Lemma lem1298761 (n : nat) (r : nat -> nat) : (term793 n r) = (term778 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298760 n r B)). Qed.
Lemma lem1298762 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298763 (n : nat) (r : nat -> nat) : (term780 n r) = (term779 n r).
Proof. exact (MK_COMB (@lem1298762) (@lem1298761 n r)). Qed.
Lemma lem1298764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1298765 (n : nat) (r : nat -> nat) : (term794 n r) = (term795 n r).
Proof. exact (MK_COMB (@lem1298764) (@lem1298763 n r)). Qed.
Lemma lem1298766 (r : nat -> nat) (n : nat) (n' : nat) : (term784 r n n') = (term760 r n n').
Proof. exact (eq_refl (term784 r n n')). Qed.
Lemma lem1298767 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298768 (r : nat -> nat) (n : nat) (n' : nat) : (term785 r n n') = (term767 r n n').
Proof. exact (MK_COMB (@lem1298767) (@lem1298766 r n n')). Qed.
Lemma lem1298769 (n : nat) (r : nat -> nat) (n' : nat) : (term786 n r n') = (term774 n r n').
Proof. exact (eq_refl (term786 n r n')). Qed.
Lemma lem1298770 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1298771 (n : nat) (r : nat -> nat) (n' : nat) : (term787 n r n') = (term788 n r n').
Proof. exact (MK_COMB (@lem1298770) (@lem1298769 n r n')). Qed.
Lemma lem1298772 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1298773 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term789 n r n' B) = (term773 n r n' B).
Proof. exact (MK_COMB (@lem1298771 n r n') (@lem1298772 B)). Qed.
Lemma lem1298774 (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term790 n r n' B) = (term775 n r n' B).
Proof. exact (MK_COMB (@lem1298768 r n n') (@lem1298773 n r n' B)). Qed.
Lemma lem1298775 (N : nat) (n' : nat) : (term796 N n') = (term796 N n').
Proof. exact (eq_refl (term796 N n')). Qed.
Lemma lem1298776 (N : nat) (n : nat) (r : nat -> nat) (n' : nat) (B : nat) : (term797 N n r n' B) = (term798 N n r n' B).
Proof. exact (MK_COMB (@lem1298775 N n') (@lem1298774 n r n' B)). Qed.
Lemma lem1298777 (N : nat) (n : nat) (r : nat -> nat) (B : nat) : (term799 N n r B) = (term800 N n r B).
Proof. exact (fun_ext (fun n' : nat => @lem1298776 N n r n' B)). Qed.
Lemma lem1298778 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1298779 (N : nat) (n : nat) (r : nat -> nat) (B : nat) : (term801 N n r B) = (term802 N n r B).
Proof. exact (MK_COMB (@lem1298778) (@lem1298777 N n r B)). Qed.
Lemma lem1298780 (n : nat) (r : nat -> nat) (B : nat) : (term803 n r B) = (term804 n r B).
Proof. exact (fun_ext (fun N : nat => @lem1298779 N n r B)). Qed.
Lemma lem1298781 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298782 (n : nat) (r : nat -> nat) (B : nat) : (term805 n r B) = (term806 n r B).
Proof. exact (MK_COMB (@lem1298781) (@lem1298780 n r B)). Qed.
Lemma lem1298783 (n : nat) (r : nat -> nat) : (term807 n r) = (term808 n r).
Proof. exact (fun_ext (fun B : nat => @lem1298782 n r B)). Qed.
Lemma lem1298784 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1298785 (n : nat) (r : nat -> nat) : (term781 n r) = (term809 n r).
Proof. exact (MK_COMB (@lem1298784) (@lem1298783 n r)). Qed.
Lemma lem1298786 (n : nat) (r : nat -> nat) : ((term780 n r) = (term781 n r)) = ((term779 n r) = (term809 n r)).
Proof. exact (MK_COMB (@lem1298765 n r) (@lem1298785 n r)). Qed.
Lemma lem1298787 (n : nat) (r : nat -> nat) : (term779 n r) = (term809 n r).
Proof. exact (EQ_MP (@lem1298786 n r) (@lem1298748 n r)). Qed.
Lemma lem1298788 (n : nat) (r : nat -> nat) : (term809 n r) = (term779 n r).
Proof. exact (SYM (@lem1298787 n r)). Qed.
Lemma lem1298789 (n : nat) (i : nat) (h1 : Peano.le n i) : Peano.le n i.
Proof. exact (h1). Qed.
Lemma lem1298791 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1296308 n m) (@lem1296307 m n)). Qed.
Lemma lem1298792 (i : nat) (r : nat -> nat) (n : nat) : (term760 r n i) = (term444 i r n).
Proof. exact (@lem1298791 i (r n)). Qed.
Lemma lem1298793 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1298794 (i : nat) (r : nat -> nat) (n : nat) : (term767 r n i) = (term541 i r n).
Proof. exact (MK_COMB (@lem1298793) (@lem1298792 i r n)). Qed.
Lemma lem1298795 (n : nat) (r : nat -> nat) (i : nat) : (term810 n r i) = (term810 n r i).
Proof. exact (eq_refl (term810 n r i)). Qed.
Lemma lem1298796 (n : nat) (r : nat -> nat) (i : nat) : (term811 n r i) = (term812 n r i).
Proof. exact (MK_COMB (@lem1298794 i r n) (@lem1298795 n r i)). Qed.
Lemma lem1298797 (n : nat) (r : nat -> nat) (i : nat) : (term812 n r i) = (term811 n r i).
Proof. exact (SYM (@lem1298796 n r i)). Qed.
Lemma lem1298799 (m : nat) (p : nat) : term77 m p.
Proof. exact (EQ_MP (@lem1296302 m p) (@lem1296301 m p)). Qed.
Lemma lem1298800 (n : nat) (r : nat -> nat) (i : nat) : term813 n r i.
Proof. exact (@lem1298799 (term444 i r n) (term810 n r i)). Qed.
Lemma lem1298801 : term45.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1298817 : term46.
Proof. exact (proj1 (@lem1298801)). Qed.
Lemma lem1298818 (m : nat) : term47 m.
Proof. exact (@lem1298817 m). Qed.
Lemma lem1298819 (m : nat) : (term47 m) = ((term48 m) = m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1298825 (m : nat) : term814 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem1298826 (m : nat) : (term814 m) = (term815 m).
Proof. exact (eq_refl (term814 m)). Qed.
Lemma lem1298827 (m : nat) : term815 m.
Proof. exact (EQ_MP (@lem1298826 m) (@lem1298825 m)). Qed.
Lemma lem1298828 (m : nat) (n : nat) : term816 m n.
Proof. exact (@lem1298827 m n). Qed.
Lemma lem1298829 (m : nat) (n : nat) : (term816 m n) = (term817 m n).
Proof. exact (eq_refl (term816 m n)). Qed.
Lemma lem1298830 (m : nat) (n : nat) : term817 m n.
Proof. exact (EQ_MP (@lem1298829 m n) (@lem1298828 m n)). Qed.
Lemma lem1298831 (m : nat) (n : nat) (p : nat) : term818 m n p.
Proof. exact (@lem1298830 m n p). Qed.
Lemma lem1298832 (m : nat) (n : nat) (p : nat) : (term818 m n p) = ((term819 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term818 m n p)). Qed.
Lemma lem1298854 (n : nat) (r : nat -> nat) (h1 : term438 r) : term634 r n.
Proof. exact (@lem1297728 r h1 n). Qed.
Lemma lem1298855 (r : nat -> nat) (n : nat) : (term634 r n) = (term522 r n).
Proof. exact (eq_refl (term634 r n)). Qed.
Lemma lem1298856 (n : nat) (r : nat -> nat) (h1 : term438 r) : term522 r n.
Proof. exact (EQ_MP (@lem1298855 r n) (@lem1298854 n r h1)). Qed.
Lemma lem1298857 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term635 r n i.
Proof. exact (@lem1298856 n r h1 i). Qed.
Lemma lem1298858 (r : nat -> nat) (i : nat) (n : nat) : (term635 r n i) = (term442 r i n).
Proof. exact (eq_refl (term635 r n i)). Qed.
Lemma lem1298859 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : term442 r i n.
Proof. exact (EQ_MP (@lem1298858 r i n) (@lem1298857 n i r h1)). Qed.
Lemma lem1298860 (r : nat -> nat) (i : nat) (n : nat) : (term442 r i n) = ((term442 r i n) = True).
Proof. exact (@lem7 (term442 r i n)). Qed.
Lemma lem1298864 (n : nat) (i : nat) : (Peano.le n i) = ((Peano.le n i) = True).
Proof. exact (@lem7 (Peano.le n i)). Qed.
Lemma lem1298869 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : (term442 r i n) = True.
Proof. exact (EQ_MP (@lem1298860 r i n) (@lem1298859 i n r h1)). Qed.
Lemma lem1298870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1298871 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : (term636 r i n) = (and True).
Proof. exact (MK_COMB (@lem1298870) (@lem1298869 i n r h1)). Qed.
Lemma lem1298875 (m : nat) : (term48 m) = m.
Proof. exact (EQ_MP (@lem1298819 m) (@lem1298818 m)). Qed.
Lemma lem1298876 (n : nat) (r : nat -> nat) (i : nat) : (term810 n r i) = (term774 n r i).
Proof. exact (@lem1298875 (term774 n r i)). Qed.
Lemma lem1298877 (r : nat -> nat) (i : nat) (n : nat) : (term638 r i n) = (term638 r i n).
Proof. exact (eq_refl (term638 r i n)). Qed.
Lemma lem1298878 (n : nat) (r : nat -> nat) (i : nat) : (term820 n r i) = (term821 n r i).
Proof. exact (MK_COMB (@lem1298877 r i n) (@lem1298876 n r i)). Qed.
Lemma lem1298880 (m : nat) (n : nat) (p : nat) : (term819 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem1298832 m n p) (@lem1298831 m n p)). Qed.
Lemma lem1298881 (r : nat -> nat) (n : nat) (i : nat) : (term821 n r i) = (Peano.le n i).
Proof. exact (@lem1298880 (term444 n r i) n i). Qed.
Lemma lem1298883 (n : nat) (i : nat) (h1 : Peano.le n i) : (Peano.le n i) = True.
Proof. exact (EQ_MP (@lem1298864 n i) (@lem1298789 n i h1)). Qed.
Lemma lem1298884 (r : nat -> nat) (n : nat) (i : nat) (h1 : Peano.le n i) : (term821 n r i) = True.
Proof. exact (TRANS (@lem1298881 r n i) (@lem1298883 n i h1)). Qed.
Lemma lem1298885 (r : nat -> nat) (n : nat) (i : nat) (h1 : Peano.le n i) : (term820 n r i) = True.
Proof. exact (TRANS (@lem1298878 n r i) (@lem1298884 r n i h1)). Qed.
Lemma lem1298886 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : (term822 n r i) = (True /\ True).
Proof. exact (MK_COMB (@lem1298871 i n r h1) (@lem1298885 r n i h2)). Qed.
Lemma lem1298888 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1298889 : (True /\ True) = True.
Proof. exact (@lem1298888 True). Qed.
Lemma lem1298890 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : (term822 n r i) = True.
Proof. exact (TRANS (@lem1298886 r n i h1 h2) (@lem1298889)). Qed.
Lemma lem1298891 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : True = (term822 n r i).
Proof. exact (SYM (@lem1298890 r n i h1 h2)). Qed.
Lemma lem1298892 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : term822 n r i.
Proof. exact (EQ_MP (@lem1298891 r n i h1 h2) (@lem0)). Qed.
Lemma lem1298893 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : term823 n r i.
Proof. exact (ex_intro (term824 n r i) (term445 r i n) (@lem1298892 r n i h1 h2)). Qed.
Lemma lem1298894 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : term812 n r i.
Proof. exact (@lem1298800 n r i (@lem1298893 r n i h1 h2)). Qed.
Lemma lem1298895 (r : nat -> nat) (n : nat) (i : nat) (h1 : term438 r) (h2 : Peano.le n i) : term811 n r i.
Proof. exact (EQ_MP (@lem1298797 n r i) (@lem1298894 r n i h1 h2)). Qed.
Lemma lem1298896 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term825 n r i.
Proof. exact (fun h0 : Peano.le n i => @lem1298895 r n i h1 h0). Qed.
Lemma lem1298901 (n : nat) (r : nat -> nat) (h1 : term438 r) : term826 n r.
Proof. exact (fun i : nat => @lem1298896 n i r h1). Qed.
Lemma lem1298902 (n : nat) (r : nat -> nat) (h1 : term438 r) : term827 n r.
Proof. exact (ex_intro (term828 n r) n (@lem1298901 n r h1)). Qed.
Lemma lem1298903 (n : nat) (r : nat -> nat) (h1 : term438 r) : term809 n r.
Proof. exact (ex_intro (term808 n r) (NUMERAL 0) (@lem1298902 n r h1)). Qed.
Lemma lem1298904 (n : nat) (r : nat -> nat) (h1 : term438 r) : term779 n r.
Proof. exact (EQ_MP (@lem1298788 n r) (@lem1298903 n r h1)). Qed.
Lemma lem1298905 (n : nat) (r : nat -> nat) (h1 : term438 r) : term772 n r.
Proof. exact (EQ_MP (@lem1298745 n r) (@lem1298904 n r h1)). Qed.
Lemma lem1298906 (n : nat) (r : nat -> nat) (h1 : term438 r) : term765 n r.
Proof. exact (EQ_MP (@lem1298725 n r) (@lem1298905 n r h1)). Qed.
Lemma lem1298907 (n : nat) (r : nat -> nat) (h1 : term438 r) : term749 n r.
Proof. exact (EQ_MP (@lem1298697 n r) (@lem1298906 n r h1)). Qed.
Lemma lem1298908 (n : nat) (r : nat -> nat) (h1 : term438 r) : term738 n r.
Proof. exact (EQ_MP (@lem1298647 n r) (@lem1298907 n r h1)). Qed.
Lemma lem1298909 (n : nat) (r : nat -> nat) (h1 : term438 r) : term732 n r.
Proof. exact (EQ_MP (@lem1298609 n r) (@lem1298908 n r h1)). Qed.
Lemma lem1298910 (n : nat) (r : nat -> nat) (h1 : term438 r) (h2 : (term145 r) = r) : term665 n r.
Proof. exact (EQ_MP (@lem1298589 n r h2) (@lem1298909 n r h1)). Qed.
Lemma lem1298911 (n : nat) (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term829 x n r.
Proof. exact (conj (@lem1298399 n r P x h1 h3) (@lem1298910 n r h2 h4)). Qed.
Lemma lem1298912 (n : nat) (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term830 x n r.
Proof. exact (ex_intro (term831 x n r) (term250 r n) (@lem1298911 n P x r h1 h2 h3 h4)). Qed.
Lemma lem1298913 (n : nat) (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term832 x n r.
Proof. exact (@lem1298339 x n r (@lem1298912 n P x r h1 h2 h3 h4)). Qed.
Lemma lem1298918 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term833 x r.
Proof. exact (fun n : nat => @lem1298913 n P x r h1 h2 h3 h4). Qed.
Lemma lem1298919 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term834 x r.
Proof. exact (ex_intro (term835 x r) term683 (@lem1298918 P x r h1 h2 h3 h4)). Qed.
Lemma lem1298920 (P : nadd -> Prop) (x : nadd) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : P x) (h4 : (term145 r) = r) : term836 x r.
Proof. exact (@lem1298336 x r (@lem1298919 P x r h1 h2 h3 h4)). Qed.
Lemma lem1298921 (x : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : (term145 r) = r) : term837 P x r.
Proof. exact (fun h0 : P x => @lem1298920 P x r h1 h2 h0 h3). Qed.
Lemma lem1298926 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : (term145 r) = r) : term838 P r.
Proof. exact (fun x : nadd => @lem1298921 x P r h1 h2 h3). Qed.
Lemma lem1298927 (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term282 P z.
Proof. exact (h1). Qed.
Lemma lem1298929 (x : nadd) (y : nadd) : term60 x y.
Proof. exact (EQ_MP (@lem1296274 x y) (@lem1296273 x y)). Qed.
Lemma lem1298930 (r : nat -> nat) (z : nadd) : term839 r z.
Proof. exact (@lem1298929 (mk_nadd r) z). Qed.
Lemma lem1298932 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296246 x z) (@lem1296245 x z)). Qed.
Lemma lem1298933 (r : nat -> nat) (n : nat) (z : nadd) : term840 r n z.
Proof. exact (@lem1298932 (term682 n r) (term841 n z)). Qed.
Lemma lem1298934 (k : nat) : term648 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1298935 (k : nat) : (term648 k) = ((term649 k) = (term650 k)).
Proof. exact (eq_refl (term648 k)). Qed.
Lemma lem1298937 (x : nadd) : term651 x.
Proof. exact (@lem1277879 x). Qed.
Lemma lem1298938 (x : nadd) : (term651 x) = (term652 x).
Proof. exact (eq_refl (term651 x)). Qed.
Lemma lem1298939 (x : nadd) : term652 x.
Proof. exact (EQ_MP (@lem1298938 x) (@lem1298937 x)). Qed.
Lemma lem1298940 (x : nadd) (y : nadd) : term653 x y.
Proof. exact (@lem1298939 x y). Qed.
Lemma lem1298941 (x : nadd) (y : nadd) : (term653 x y) = ((term654 x y) = (term655 x y)).
Proof. exact (eq_refl (term653 x y)). Qed.
Lemma lem1298943 (x : nadd) : term656 x.
Proof. exact (@lem1274104 x). Qed.
Lemma lem1298944 (x : nadd) : (term656 x) = (term657 x).
Proof. exact (eq_refl (term656 x)). Qed.
Lemma lem1298945 (x : nadd) : term657 x.
Proof. exact (EQ_MP (@lem1298944 x) (@lem1298943 x)). Qed.
Lemma lem1298946 (x : nadd) (y : nadd) : term658 x y.
Proof. exact (@lem1298945 x y). Qed.
Lemma lem1298947 (x : nadd) (y : nadd) : (term658 x y) = ((term659 x y) = (term660 x y)).
Proof. exact (eq_refl (term658 x y)). Qed.
Lemma lem1298949 (x : nadd) : term661 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1298950 (x : nadd) : (term661 x) = (term662 x).
Proof. exact (eq_refl (term661 x)). Qed.
Lemma lem1298951 (x : nadd) : term662 x.
Proof. exact (EQ_MP (@lem1298950 x) (@lem1298949 x)). Qed.
Lemma lem1298952 (x : nadd) (y : nadd) : term663 x y.
Proof. exact (@lem1298951 x y). Qed.
Lemma lem1298953 (x : nadd) (y : nadd) : (term663 x y) = ((nadd_le x y) = (term664 x y)).
Proof. exact (eq_refl (term663 x y)). Qed.
Lemma lem1298989 (x : nadd) (y : nadd) : (nadd_le x y) = (term664 x y).
Proof. exact (EQ_MP (@lem1298953 x y) (@lem1298952 x y)). Qed.
Lemma lem1298990 (r : nat -> nat) (n : nat) : (term842 r n) = (term843 r n).
Proof. exact (@lem1298989 (term682 n r) (term844 r n)). Qed.
Lemma lem1299000 (x : nadd) (y : nadd) : (term654 x y) = (term655 x y).
Proof. exact (EQ_MP (@lem1298941 x y) (@lem1298940 x y)). Qed.
Lemma lem1299001 (n : nat) (r : nat -> nat) : (term684 n r) = (term685 n r).
Proof. exact (@lem1299000 (nadd_of_num n) (mk_nadd r)). Qed.
Lemma lem1299003 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298935 k) (@lem1298934 k)). Qed.
Lemma lem1299004 (n : nat) : (term649 n) = (term650 n).
Proof. exact (@lem1299003 n). Qed.
Lemma lem1299006 (r : nat -> nat) (h1 : (term145 r) = r) : (term145 r) = r.
Proof. exact (h1). Qed.
Lemma lem1299007 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299008 (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term686 r n') = (r n').
Proof. exact (MK_COMB (@lem1299006 r h1) (@lem1299007 n')). Qed.
Lemma lem1299009 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term687 n r n') = (term688 n r n').
Proof. exact (MK_COMB (@lem1299004 n) (@lem1299008 n' r h1)). Qed.
Lemma lem1299011 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299012 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1299011 nat nat f y). Qed.
Lemma lem1299013 (n : nat) (r : nat -> nat) (n' : nat) : (term689 n r n') = (term688 n r n').
Proof. exact (@lem1299012 (term650 n) (r n')). Qed.
Lemma lem1299014 (n : nat) (n' : nat) : (term690 n n') = (Nat.mul n n').
Proof. exact (eq_refl (term690 n n')). Qed.
Lemma lem1299015 (n : nat) : (term691 n) = (term650 n).
Proof. exact (fun_ext (fun n' : nat => @lem1299014 n n')). Qed.
Lemma lem1299016 (r : nat -> nat) (n' : nat) : (r n') = (r n').
Proof. exact (eq_refl (r n')). Qed.
Lemma lem1299017 (n : nat) (r : nat -> nat) (n' : nat) : (term689 n r n') = (term688 n r n').
Proof. exact (MK_COMB (@lem1299015 n) (@lem1299016 r n')). Qed.
Lemma lem1299018 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299019 (n : nat) (r : nat -> nat) (n' : nat) : (term692 n r n') = (term693 n r n').
Proof. exact (MK_COMB (@lem1299018) (@lem1299017 n r n')). Qed.
Lemma lem1299020 (n : nat) (r : nat -> nat) (n' : nat) : (term688 n r n') = (term444 n r n').
Proof. exact (eq_refl (term688 n r n')). Qed.
Lemma lem1299021 (n : nat) (r : nat -> nat) (n' : nat) : ((term689 n r n') = (term688 n r n')) = ((term688 n r n') = (term444 n r n')).
Proof. exact (MK_COMB (@lem1299019 n r n') (@lem1299020 n r n')). Qed.
Lemma lem1299022 (n : nat) (r : nat -> nat) (n' : nat) : (term688 n r n') = (term444 n r n').
Proof. exact (EQ_MP (@lem1299021 n r n') (@lem1299013 n r n')). Qed.
Lemma lem1299023 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term687 n r n') = (term444 n r n').
Proof. exact (TRANS (@lem1299009 n n' r h1) (@lem1299022 n r n')). Qed.
Lemma lem1299024 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term685 n r) = (term694 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1299023 n n' r h1)). Qed.
Lemma lem1299025 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term684 n r) = (term694 n r).
Proof. exact (TRANS (@lem1299001 n r) (@lem1299024 n r h1)). Qed.
Lemma lem1299026 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299027 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term695 n r n') = (term696 n r n').
Proof. exact (MK_COMB (@lem1299025 n r h1) (@lem1299026 n')). Qed.
Lemma lem1299029 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299030 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1299029 nat nat f y). Qed.
Lemma lem1299031 (n : nat) (r : nat -> nat) (n' : nat) : (term697 n r n') = (term696 n r n').
Proof. exact (@lem1299030 (term694 n r) n'). Qed.
Lemma lem1299032 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (eq_refl (term696 n r n')). Qed.
Lemma lem1299033 (n : nat) (r : nat -> nat) : (term698 n r) = (term694 n r).
Proof. exact (fun_ext (fun n' : nat => @lem1299032 n r n')). Qed.
Lemma lem1299034 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299035 (n : nat) (r : nat -> nat) (n' : nat) : (term697 n r n') = (term696 n r n').
Proof. exact (MK_COMB (@lem1299033 n r) (@lem1299034 n')). Qed.
Lemma lem1299036 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299037 (n : nat) (r : nat -> nat) (n' : nat) : (term699 n r n') = (term700 n r n').
Proof. exact (MK_COMB (@lem1299036) (@lem1299035 n r n')). Qed.
Lemma lem1299038 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (eq_refl (term696 n r n')). Qed.
Lemma lem1299039 (n : nat) (r : nat -> nat) (n' : nat) : ((term697 n r n') = (term696 n r n')) = ((term696 n r n') = (term444 n r n')).
Proof. exact (MK_COMB (@lem1299037 n r n') (@lem1299038 n r n')). Qed.
Lemma lem1299040 (n : nat) (r : nat -> nat) (n' : nat) : (term696 n r n') = (term444 n r n').
Proof. exact (EQ_MP (@lem1299039 n r n') (@lem1299031 n r n')). Qed.
Lemma lem1299041 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term695 n r n') = (term444 n r n').
Proof. exact (TRANS (@lem1299027 n n' r h1) (@lem1299040 n r n')). Qed.
Lemma lem1299042 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1299043 (n : nat) (n' : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term845 n r n') = (term541 n r n').
Proof. exact (MK_COMB (@lem1299042) (@lem1299041 n n' r h1)). Qed.
Lemma lem1299045 (x : nadd) (y : nadd) : (term659 x y) = (term660 x y).
Proof. exact (EQ_MP (@lem1298947 x y) (@lem1298946 x y)). Qed.
Lemma lem1299046 (r : nat -> nat) (n : nat) : (term846 r n) = (term847 r n).
Proof. exact (@lem1299045 (term457 r n) term848). Qed.
Lemma lem1299048 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298935 k) (@lem1298934 k)). Qed.
Lemma lem1299049 (r : nat -> nat) (n : nat) : (term849 r n) = (term782 r n).
Proof. exact (@lem1299048 (r n)). Qed.
Lemma lem1299050 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299051 (r : nat -> nat) (n : nat) (n' : nat) : (term850 r n n') = (term784 r n n').
Proof. exact (MK_COMB (@lem1299049 r n) (@lem1299050 n')). Qed.
Lemma lem1299053 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299054 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1299053 nat nat f y). Qed.
Lemma lem1299055 (r : nat -> nat) (n : nat) (n' : nat) : (term851 r n n') = (term784 r n n').
Proof. exact (@lem1299054 (term782 r n) n'). Qed.
Lemma lem1299056 (r : nat -> nat) (n : nat) (n' : nat) : (term784 r n n') = (term760 r n n').
Proof. exact (eq_refl (term784 r n n')). Qed.
Lemma lem1299057 (r : nat -> nat) (n : nat) : (term852 r n) = (term782 r n).
Proof. exact (fun_ext (fun n' : nat => @lem1299056 r n n')). Qed.
Lemma lem1299058 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299059 (r : nat -> nat) (n : nat) (n' : nat) : (term851 r n n') = (term784 r n n').
Proof. exact (MK_COMB (@lem1299057 r n) (@lem1299058 n')). Qed.
Lemma lem1299060 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299061 (r : nat -> nat) (n : nat) (n' : nat) : (term853 r n n') = (term854 r n n').
Proof. exact (MK_COMB (@lem1299060) (@lem1299059 r n n')). Qed.
Lemma lem1299062 (r : nat -> nat) (n : nat) (n' : nat) : (term784 r n n') = (term760 r n n').
Proof. exact (eq_refl (term784 r n n')). Qed.
Lemma lem1299063 (r : nat -> nat) (n : nat) (n' : nat) : ((term851 r n n') = (term784 r n n')) = ((term784 r n n') = (term760 r n n')).
Proof. exact (MK_COMB (@lem1299061 r n n') (@lem1299062 r n n')). Qed.
Lemma lem1299064 (r : nat -> nat) (n : nat) (n' : nat) : (term784 r n n') = (term760 r n n').
Proof. exact (EQ_MP (@lem1299063 r n n') (@lem1299055 r n n')). Qed.
Lemma lem1299065 (r : nat -> nat) (n : nat) (n' : nat) : (term850 r n n') = (term760 r n n').
Proof. exact (TRANS (@lem1299051 r n n') (@lem1299064 r n n')). Qed.
Lemma lem1299066 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299067 (r : nat -> nat) (n : nat) (n' : nat) : (term855 r n n') = (term750 r n n').
Proof. exact (MK_COMB (@lem1299066) (@lem1299065 r n n')). Qed.
Lemma lem1299069 (k : nat) : (term649 k) = (term650 k).
Proof. exact (EQ_MP (@lem1298935 k) (@lem1298934 k)). Qed.
Lemma lem1299070 : term856 = term857.
Proof. exact (@lem1299069 term644). Qed.
Lemma lem1299071 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299072 (n' : nat) : (term858 n') = (term859 n').
Proof. exact (MK_COMB (@lem1299070) (@lem1299071 n')). Qed.
Lemma lem1299074 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299075 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1299074 nat nat f y). Qed.
Lemma lem1299076 (n' : nat) : (term860 n') = (term859 n').
Proof. exact (@lem1299075 term857 n'). Qed.
Lemma lem1299077 (n : nat) : (term859 n) = (term44 n).
Proof. exact (eq_refl (term859 n)). Qed.
Lemma lem1299078 : term861 = term857.
Proof. exact (fun_ext (fun n : nat => @lem1299077 n)). Qed.
Lemma lem1299079 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299080 (n' : nat) : (term860 n') = (term859 n').
Proof. exact (MK_COMB (@lem1299078) (@lem1299079 n')). Qed.
Lemma lem1299081 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299082 (n' : nat) : (term862 n') = (term863 n').
Proof. exact (MK_COMB (@lem1299081) (@lem1299080 n')). Qed.
Lemma lem1299083 (n' : nat) : (term859 n') = (term44 n').
Proof. exact (eq_refl (term859 n')). Qed.
Lemma lem1299084 (n' : nat) : ((term860 n') = (term859 n')) = ((term859 n') = (term44 n')).
Proof. exact (MK_COMB (@lem1299082 n') (@lem1299083 n')). Qed.
Lemma lem1299085 (n' : nat) : (term859 n') = (term44 n').
Proof. exact (EQ_MP (@lem1299084 n') (@lem1299076 n')). Qed.
Lemma lem1299086 (n' : nat) : (term858 n') = (term44 n').
Proof. exact (TRANS (@lem1299072 n') (@lem1299085 n')). Qed.
Lemma lem1299087 (r : nat -> nat) (n : nat) (n' : nat) : (term864 r n n') = (term743 r n n').
Proof. exact (MK_COMB (@lem1299067 r n n') (@lem1299086 n')). Qed.
Lemma lem1299088 (r : nat -> nat) (n : nat) : (term847 r n) = (term865 r n).
Proof. exact (fun_ext (fun n' : nat => @lem1299087 r n n')). Qed.
Lemma lem1299089 (r : nat -> nat) (n : nat) : (term846 r n) = (term865 r n).
Proof. exact (TRANS (@lem1299046 r n) (@lem1299088 r n)). Qed.
Lemma lem1299090 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299091 (r : nat -> nat) (n : nat) (n' : nat) : (term866 r n n') = (term867 r n n').
Proof. exact (MK_COMB (@lem1299089 r n) (@lem1299090 n')). Qed.
Lemma lem1299093 {A B : Type'} (f : A -> B) (y : A) : (term671 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1299094 (f : nat -> nat) (y : nat) : (term672 f y) = (f y).
Proof. exact (@lem1299093 nat nat f y). Qed.
Lemma lem1299095 (r : nat -> nat) (n : nat) (n' : nat) : (term868 r n n') = (term867 r n n').
Proof. exact (@lem1299094 (term865 r n) n'). Qed.
Lemma lem1299096 (r : nat -> nat) (n : nat) (n' : nat) : (term867 r n n') = (term743 r n n').
Proof. exact (eq_refl (term867 r n n')). Qed.
Lemma lem1299097 (r : nat -> nat) (n : nat) : (term869 r n) = (term865 r n).
Proof. exact (fun_ext (fun n' : nat => @lem1299096 r n n')). Qed.
Lemma lem1299098 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299099 (r : nat -> nat) (n : nat) (n' : nat) : (term868 r n n') = (term867 r n n').
Proof. exact (MK_COMB (@lem1299097 r n) (@lem1299098 n')). Qed.
Lemma lem1299100 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1299101 (r : nat -> nat) (n : nat) (n' : nat) : (term870 r n n') = (term871 r n n').
Proof. exact (MK_COMB (@lem1299100) (@lem1299099 r n n')). Qed.
Lemma lem1299102 (r : nat -> nat) (n : nat) (n' : nat) : (term867 r n n') = (term743 r n n').
Proof. exact (eq_refl (term867 r n n')). Qed.
Lemma lem1299103 (r : nat -> nat) (n : nat) (n' : nat) : ((term868 r n n') = (term867 r n n')) = ((term867 r n n') = (term743 r n n')).
Proof. exact (MK_COMB (@lem1299101 r n n') (@lem1299102 r n n')). Qed.
Lemma lem1299104 (r : nat -> nat) (n : nat) (n' : nat) : (term867 r n n') = (term743 r n n').
Proof. exact (EQ_MP (@lem1299103 r n n') (@lem1299095 r n n')). Qed.
Lemma lem1299105 (r : nat -> nat) (n : nat) (n' : nat) : (term866 r n n') = (term743 r n n').
Proof. exact (TRANS (@lem1299091 r n n') (@lem1299104 r n n')). Qed.
Lemma lem1299106 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299107 (r : nat -> nat) (n : nat) (n' : nat) : (term872 r n n') = (term873 r n n').
Proof. exact (MK_COMB (@lem1299106) (@lem1299105 r n n')). Qed.
Lemma lem1299108 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1299109 (r : nat -> nat) (n : nat) (n' : nat) (B : nat) : (term874 r n n' B) = (term875 r n n' B).
Proof. exact (MK_COMB (@lem1299107 r n n') (@lem1299108 B)). Qed.
Lemma lem1299110 (n : nat) (n' : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term876 r n n' B) = (term877 r n n' B).
Proof. exact (MK_COMB (@lem1299043 n n' r h1) (@lem1299109 r n n' B)). Qed.
Lemma lem1299111 (n : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term878 r n B) = (term879 r n B).
Proof. exact (fun_ext (fun n' : nat => @lem1299110 n n' B r h1)). Qed.
Lemma lem1299112 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299113 (n : nat) (B : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term880 r n B) = (term881 r n B).
Proof. exact (MK_COMB (@lem1299112) (@lem1299111 n B r h1)). Qed.
Lemma lem1299118 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term882 r n) = (term883 r n).
Proof. exact (fun_ext (fun B : nat => @lem1299113 n B r h1)). Qed.
Lemma lem1299119 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1299120 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term843 r n) = (term884 r n).
Proof. exact (MK_COMB (@lem1299119) (@lem1299118 n r h1)). Qed.
Lemma lem1299125 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term842 r n) = (term884 r n).
Proof. exact (TRANS (@lem1298990 r n) (@lem1299120 n r h1)). Qed.
Lemma lem1299126 (n : nat) (r : nat -> nat) (h1 : (term145 r) = r) : (term884 r n) = (term842 r n).
Proof. exact (SYM (@lem1299125 n r h1)). Qed.
Lemma lem1299132 (m : nat) : (term48 m) = m.
Proof. exact (EQ_MP (@lem1296214 m) (@lem1296213 m)). Qed.
Lemma lem1299133 (r : nat -> nat) (n : nat) (n' : nat) : (term885 r n n') = (term743 r n n').
Proof. exact (@lem1299132 (term743 r n n')). Qed.
Lemma lem1299135 (n : nat) : (term44 n) = n.
Proof. exact (EQ_MP (@lem1296186 n) (@lem1296185 n)). Qed.
Lemma lem1299136 (n' : nat) : (term44 n') = n'.
Proof. exact (@lem1299135 n'). Qed.
Lemma lem1299137 (r : nat -> nat) (n : nat) (n' : nat) : (term750 r n n') = (term750 r n n').
Proof. exact (eq_refl (term750 r n n')). Qed.
Lemma lem1299138 (r : nat -> nat) (n : nat) (n' : nat) : (term743 r n n') = (term751 r n n').
Proof. exact (MK_COMB (@lem1299137 r n n') (@lem1299136 n')). Qed.
Lemma lem1299139 (r : nat -> nat) (n : nat) (n' : nat) : (term885 r n n') = (term751 r n n').
Proof. exact (TRANS (@lem1299133 r n n') (@lem1299138 r n n')). Qed.
Lemma lem1299140 (n : nat) (r : nat -> nat) (n' : nat) : (term541 n r n') = (term541 n r n').
Proof. exact (eq_refl (term541 n r n')). Qed.
Lemma lem1299141 (r : nat -> nat) (n : nat) (n' : nat) : (term886 r n n') = (term887 r n n').
Proof. exact (MK_COMB (@lem1299140 n r n') (@lem1299139 r n n')). Qed.
Lemma lem1299142 (r : nat -> nat) (n : nat) : (term888 r n) = (term889 r n).
Proof. exact (fun_ext (fun n' : nat => @lem1299141 r n n')). Qed.
Lemma lem1299143 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1299144 (r : nat -> nat) (n : nat) : (term890 r n) = (term891 r n).
Proof. exact (MK_COMB (@lem1299143) (@lem1299142 r n)). Qed.
Lemma lem1299149 (r : nat -> nat) (n : nat) : (term891 r n) = (term890 r n).
Proof. exact (SYM (@lem1299144 r n)). Qed.
Lemma lem1299151 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1296160 n m) (@lem1296159 m n)). Qed.
Lemma lem1299152 (n' : nat) (r : nat -> nat) (n : nat) : (term760 r n n') = (term444 n' r n).
Proof. exact (@lem1299151 n' (r n)). Qed.
Lemma lem1299153 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1299154 (n' : nat) (r : nat -> nat) (n : nat) : (term750 r n n') = (term538 n' r n).
Proof. exact (MK_COMB (@lem1299153) (@lem1299152 n' r n)). Qed.
Lemma lem1299155 (n' : nat) : n' = n'.
Proof. exact (eq_refl n'). Qed.
Lemma lem1299156 (r : nat -> nat) (n : nat) (n' : nat) : (term751 r n n') = (term445 r n n').
Proof. exact (MK_COMB (@lem1299154 n' r n) (@lem1299155 n')). Qed.
Lemma lem1299157 (n : nat) (r : nat -> nat) (n' : nat) : (term541 n r n') = (term541 n r n').
Proof. exact (eq_refl (term541 n r n')). Qed.
Lemma lem1299158 (r : nat -> nat) (n : nat) (n' : nat) : (term887 r n n') = (term442 r n n').
Proof. exact (MK_COMB (@lem1299157 n r n') (@lem1299156 r n n')). Qed.
Lemma lem1299159 (r : nat -> nat) (n : nat) (n' : nat) : (term442 r n n') = (term887 r n n').
Proof. exact (SYM (@lem1299158 r n n')). Qed.
Lemma lem1299180 (n : nat) (r : nat -> nat) (h1 : term438 r) : term634 r n.
Proof. exact (@lem1297728 r h1 n). Qed.
Lemma lem1299181 (r : nat -> nat) (n : nat) : (term634 r n) = (term522 r n).
Proof. exact (eq_refl (term634 r n)). Qed.
Lemma lem1299182 (n : nat) (r : nat -> nat) (h1 : term438 r) : term522 r n.
Proof. exact (EQ_MP (@lem1299181 r n) (@lem1299180 n r h1)). Qed.
Lemma lem1299183 (n : nat) (i : nat) (r : nat -> nat) (h1 : term438 r) : term635 r n i.
Proof. exact (@lem1299182 n r h1 i). Qed.
Lemma lem1299184 (r : nat -> nat) (i : nat) (n : nat) : (term635 r n i) = (term442 r i n).
Proof. exact (eq_refl (term635 r n i)). Qed.
Lemma lem1299185 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : term442 r i n.
Proof. exact (EQ_MP (@lem1299184 r i n) (@lem1299183 n i r h1)). Qed.
Lemma lem1299186 (r : nat -> nat) (i : nat) (n : nat) : (term442 r i n) = ((term442 r i n) = True).
Proof. exact (@lem7 (term442 r i n)). Qed.
Lemma lem1299194 (i : nat) (n : nat) (r : nat -> nat) (h1 : term438 r) : (term442 r i n) = True.
Proof. exact (EQ_MP (@lem1299186 r i n) (@lem1299185 i n r h1)). Qed.
Lemma lem1299195 (n : nat) (n' : nat) (r : nat -> nat) (h1 : term438 r) : (term442 r n n') = True.
Proof. exact (@lem1299194 n n' r h1). Qed.
Lemma lem1299196 (n : nat) (n' : nat) (r : nat -> nat) (h1 : term438 r) : True = (term442 r n n').
Proof. exact (SYM (@lem1299195 n n' r h1)). Qed.
Lemma lem1299197 (n : nat) (n' : nat) (r : nat -> nat) (h1 : term438 r) : term442 r n n'.
Proof. exact (EQ_MP (@lem1299196 n n' r h1) (@lem0)). Qed.
Lemma lem1299198 (n : nat) (n' : nat) (r : nat -> nat) (h1 : term438 r) : term887 r n n'.
Proof. exact (EQ_MP (@lem1299159 r n n') (@lem1299197 n n' r h1)). Qed.
Lemma lem1299203 (n : nat) (r : nat -> nat) (h1 : term438 r) : term891 r n.
Proof. exact (fun n' : nat => @lem1299198 n n' r h1). Qed.
Lemma lem1299204 (n : nat) (r : nat -> nat) (h1 : term438 r) : term890 r n.
Proof. exact (EQ_MP (@lem1299149 r n) (@lem1299203 n r h1)). Qed.
Lemma lem1299205 (n : nat) (r : nat -> nat) (h1 : term438 r) : term884 r n.
Proof. exact (ex_intro (term883 r n) (NUMERAL 0) (@lem1299204 n r h1)). Qed.
Lemma lem1299206 (n : nat) (r : nat -> nat) (h1 : term438 r) (h2 : (term145 r) = r) : term842 r n.
Proof. exact (EQ_MP (@lem1299126 n r h2) (@lem1299205 n r h1)). Qed.
Lemma lem1299208 (z : nadd) (x : nadd) (y : nadd) : (term36 x y z) = (nadd_le x y).
Proof. exact (EQ_MP (@lem1296154 z x y) (@lem1296153 x y z)). Qed.
Lemma lem1299209 (r : nat -> nat) (n : nat) (z : nadd) : (term892 r n z) = (term441 r n z).
Proof. exact (@lem1299208 term848 (term457 r n) (term247 n z)). Qed.
Lemma lem1299210 (r : nat -> nat) (n : nat) (z : nadd) : (term441 r n z) = (term892 r n z).
Proof. exact (SYM (@lem1299209 r n z)). Qed.
Lemma lem1299214 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term391 P r) : term439 P r n.
Proof. exact (@lem1297727 P r h1 n). Qed.
Lemma lem1299215 (P : nadd -> Prop) (r : nat -> nat) (n : nat) : (term439 P r n) = (term390 P r n).
Proof. exact (eq_refl (term439 P r n)). Qed.
Lemma lem1299216 (n : nat) (P : nadd -> Prop) (r : nat -> nat) (h1 : term391 P r) : term390 P r n.
Proof. exact (EQ_MP (@lem1299215 P r n) (@lem1299214 n P r h1)). Qed.
Lemma lem1299217 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : term440 P r n x.
Proof. exact (h1). Qed.
Lemma lem1299218 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : term440 P r n x.
Proof. exact (h1). Qed.
Lemma lem1299219 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : term441 r n x.
Proof. exact (h1). Qed.
Lemma lem1299220 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1299222 (x : nadd) (z : nadd) : term25 x z.
Proof. exact (EQ_MP (@lem1296145 x z) (@lem1296144 x z)). Qed.
Lemma lem1299223 (r : nat -> nat) (n : nat) (z : nadd) : term893 r n z.
Proof. exact (@lem1299222 (term457 r n) (term247 n z)). Qed.
Lemma lem1299259 (r : nat -> nat) (n : nat) (x : nadd) : (term441 r n x) = ((term441 r n x) = True).
Proof. exact (@lem7 (term441 r n x)). Qed.
Lemma lem1299264 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term441 r n x) = True.
Proof. exact (EQ_MP (@lem1299259 r n x) (@lem1299219 r n x h1)). Qed.
Lemma lem1299265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1299266 (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term894 r n x) = (and True).
Proof. exact (MK_COMB (@lem1299265) (@lem1299264 r n x h1)). Qed.
Lemma lem1299267 (x : nadd) (n : nat) (z : nadd) : (term895 x n z) = (term895 x n z).
Proof. exact (eq_refl (term895 x n z)). Qed.
Lemma lem1299268 (z : nadd) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term896 r x n z) = (term897 x n z).
Proof. exact (MK_COMB (@lem1299266 r n x h1) (@lem1299267 x n z)). Qed.
Lemma lem1299270 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1299271 (x : nadd) (n : nat) (z : nadd) : (term897 x n z) = (term895 x n z).
Proof. exact (@lem1299270 (term895 x n z)). Qed.
Lemma lem1299272 (z : nadd) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term896 r x n z) = (term895 x n z).
Proof. exact (TRANS (@lem1299268 z r n x h1) (@lem1299271 x n z)). Qed.
Lemma lem1299273 (z : nadd) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term441 r n x) : (term895 x n z) = (term896 r x n z).
Proof. exact (SYM (@lem1299272 z r n x h1)). Qed.
Lemma lem1299275 (y : nadd) (x : nadd) (z : nadd) : term6 y x z.
Proof. exact (EQ_MP (@lem1296117 y x z) (@lem1296116 y x z)). Qed.
Lemma lem1299276 (x : nadd) (n : nat) (z : nadd) : term898 x n z.
Proof. exact (@lem1299275 x (nadd_of_num n) z). Qed.
Lemma lem1299277 (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term282 P z.
Proof. exact (h1). Qed.
Lemma lem1299278 (x : nadd) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term340 P z x.
Proof. exact (@lem1299277 P z h1 x). Qed.
Lemma lem1299279 (P : nadd -> Prop) (x : nadd) (z : nadd) : (term340 P z x) = (term341 P x z).
Proof. exact (eq_refl (term340 P z x)). Qed.
Lemma lem1299280 (x : nadd) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term341 P x z.
Proof. exact (EQ_MP (@lem1299279 P x z) (@lem1299278 x P z h1)). Qed.
Lemma lem1299281 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (h1). Qed.
Lemma lem1299282 (z : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P z) (h2 : P x) : nadd_le x z.
Proof. exact (@lem1299280 x P z h1 (@lem1299281 P x h2)). Qed.
Lemma lem1299283 (z : nadd) (P : nadd -> Prop) (x : nadd) (h1 : P x) : term342 P x z.
Proof. exact (fun h0 : term282 P z => @lem1299282 z P x h0 h1). Qed.
Lemma lem1299284 (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term282 P z.
Proof. exact (h1). Qed.
Lemma lem1299285 (z : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P z) (h2 : P x) : nadd_le x z.
Proof. exact (@lem1299283 z P x h2 (@lem1299284 P z h1)). Qed.
Lemma lem1299286 (x : nadd) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term341 P x z.
Proof. exact (fun h0 : P x => @lem1299285 z P x h1 h0). Qed.
Lemma lem1299287 (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term282 P z.
Proof. exact (fun x : nadd => @lem1299286 x P z h1). Qed.
Lemma lem1299288 (P : nadd -> Prop) (z : nadd) : term343 P z.
Proof. exact (fun h0 : term282 P z => @lem1299287 P z h0). Qed.
Lemma lem1299289 (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term282 P z.
Proof. exact (@lem1299288 P z (@lem1298927 P z h1)). Qed.
Lemma lem1299290 (x : nadd) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term340 P z x.
Proof. exact (@lem1299289 P z h1 x). Qed.
Lemma lem1299291 (P : nadd -> Prop) (x : nadd) (z : nadd) : (term340 P z x) = (term341 P x z).
Proof. exact (eq_refl (term340 P z x)). Qed.
Lemma lem1299294 (x : nadd) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term341 P x z.
Proof. exact (EQ_MP (@lem1299291 P x z) (@lem1299290 x P z h1)). Qed.
Lemma lem1299328 (P : nadd -> Prop) (x : nadd) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem1299333 (P : nadd -> Prop) (x : nadd) (h1 : P x) : (P x) = True.
Proof. exact (EQ_MP (@lem1299328 P x) (@lem1299220 P x h1)). Qed.
Lemma lem1299334 (P : nadd -> Prop) (x : nadd) (h1 : P x) : True = (P x).
Proof. exact (SYM (@lem1299333 P x h1)). Qed.
Lemma lem1299335 (P : nadd -> Prop) (x : nadd) (h1 : P x) : P x.
Proof. exact (EQ_MP (@lem1299334 P x h1) (@lem0)). Qed.
Lemma lem1299336 (z : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P z) (h2 : P x) : nadd_le x z.
Proof. exact (@lem1299294 x P z h1 (@lem1299335 P x h2)). Qed.
Lemma lem1299337 (n : nat) (z : nadd) (P : nadd -> Prop) (x : nadd) (h1 : term282 P z) (h2 : P x) : term895 x n z.
Proof. exact (@lem1299276 x n z (@lem1299336 z P x h1 h2)). Qed.
Lemma lem1299338 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : term896 r x n z.
Proof. exact (EQ_MP (@lem1299273 z r n x h3) (@lem1299337 n z P x h1 h2)). Qed.
Lemma lem1299339 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : term899 r n z.
Proof. exact (ex_intro (term900 r n z) (term247 n x) (@lem1299338 z P r n x h1 h2 h3)). Qed.
Lemma lem1299340 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : term441 r n z.
Proof. exact (@lem1299223 r n z (@lem1299339 z P r n x h1 h2 h3)). Qed.
Lemma lem1299341 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : term441 r n x.
Proof. exact (proj2 (@lem1299218 P r n x h1)). Qed.
Lemma lem1299342 (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term440 P r n x) : P x.
Proof. exact (proj1 (@lem1299218 P r n x h1)). Qed.
Lemma lem1299343 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : (term441 r n x) = (term441 r n z).
Proof. exact (prop_ext (fun h4 : term441 r n x => @lem1299340 z P r n x h1 h2 h3) (fun h4 : term441 r n z => @lem1299219 r n x h3)). Qed.
Lemma lem1299344 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : term441 r n z.
Proof. exact (EQ_MP (@lem1299343 z P r n x h1 h2 h3) (@lem1299219 r n x h3)). Qed.
Lemma lem1299345 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : (P x) = (term441 r n z).
Proof. exact (prop_ext (fun h4 : P x => @lem1299344 z P r n x h1 h2 h3) (fun h4 : term441 r n z => @lem1299220 P x h2)). Qed.
Lemma lem1299346 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term441 r n x) : term441 r n z.
Proof. exact (EQ_MP (@lem1299345 z P r n x h1 h2 h3) (@lem1299220 P x h2)). Qed.
Lemma lem1299347 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term440 P r n x) : (term441 r n x) = (term441 r n z).
Proof. exact (prop_ext (fun h4 : term441 r n x => @lem1299346 z P r n x h1 h2 h4) (fun h4 : term441 r n z => @lem1299341 P r n x h3)). Qed.
Lemma lem1299348 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : P x) (h3 : term440 P r n x) : term441 r n z.
Proof. exact (EQ_MP (@lem1299347 z P r n x h1 h2 h3) (@lem1299341 P r n x h3)). Qed.
Lemma lem1299349 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : term440 P r n x) : (P x) = (term441 r n z).
Proof. exact (prop_ext (fun h3 : P x => @lem1299348 z P r n x h1 h3 h2) (fun h3 : term441 r n z => @lem1299342 P r n x h2)). Qed.
Lemma lem1299350 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : term440 P r n x) : term441 r n z.
Proof. exact (EQ_MP (@lem1299349 z P r n x h1 h2) (@lem1299342 P r n x h2)). Qed.
Lemma lem1299351 (x : nadd) (r : nat -> nat) (n : nat) (P : nadd -> Prop) (z : nadd) (h1 : term282 P z) : term901 P x r n z.
Proof. exact (fun h0 : term440 P r n x => @lem1299350 z P r n x h1 h0). Qed.
Lemma lem1299352 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (n : nat) (x : nadd) (h1 : term282 P z) (h2 : term440 P r n x) : term441 r n z.
Proof. exact (@lem1299351 x r n P z h1 (@lem1299217 P r n x h2)). Qed.
Lemma lem1299353 (n : nat) (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term391 P r) : term441 r n z.
Proof. exact (ex_elim (@lem1299216 n P r h2) (fun x : nadd => fun h0 : term521 P r n x => @lem1299352 z P r n x h1 h0)). Qed.
Lemma lem1299354 (n : nat) (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term391 P r) : term892 r n z.
Proof. exact (EQ_MP (@lem1299210 r n z) (@lem1299353 n z P r h1 h2)). Qed.
Lemma lem1299355 (n : nat) (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term902 r n z.
Proof. exact (conj (@lem1299206 n r h2 h4) (@lem1299354 n z P r h1 h3)). Qed.
Lemma lem1299356 (n : nat) (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term903 r n z.
Proof. exact (ex_intro (term904 r n z) (term844 r n) (@lem1299355 n z P r h1 h2 h3 h4)). Qed.
Lemma lem1299357 (n : nat) (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term905 r n z.
Proof. exact (@lem1298933 r n z (@lem1299356 n z P r h1 h2 h3 h4)). Qed.
Lemma lem1299362 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term906 r z.
Proof. exact (fun n : nat => @lem1299357 n z P r h1 h2 h3 h4). Qed.
Lemma lem1299363 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term907 r z.
Proof. exact (ex_intro (term908 r z) term848 (@lem1299362 z P r h1 h2 h3 h4)). Qed.
Lemma lem1299364 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term282 P z) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term909 r z.
Proof. exact (@lem1298930 r z (@lem1299363 z P r h1 h2 h3 h4)). Qed.
Lemma lem1299365 (z : nadd) (P : nadd -> Prop) (r : nat -> nat) (h1 : term438 r) (h2 : term391 P r) (h3 : (term145 r) = r) : term910 P r z.
Proof. exact (fun h0 : term282 P z => @lem1299364 z P r h0 h1 h2 h3). Qed.
Lemma lem1299370 (P : nadd -> Prop) (r : nat -> nat) (h1 : term438 r) (h2 : term391 P r) (h3 : (term145 r) = r) : term911 P r.
Proof. exact (fun z : nadd => @lem1299365 z P r h1 h2 h3). Qed.
Lemma lem1299371 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term912 P r.
Proof. exact (conj (@lem1298926 P r h1 h2 h4) (@lem1299370 P r h2 h3 h4)). Qed.
Lemma lem1299372 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : ((term145 r) = r) = (term912 P r).
Proof. exact (prop_ext (fun h5 : (term145 r) = r => @lem1299371 P r h1 h2 h3 h4) (fun h5 : term912 P r => @lem1297983 r h4)). Qed.
Lemma lem1299373 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) (h4 : (term145 r) = r) : term912 P r.
Proof. exact (EQ_MP (@lem1299372 P r h1 h2 h3 h4) (@lem1297983 r h4)). Qed.
Lemma lem1299374 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) : ((term145 r) = r) = (term912 P r).
Proof. exact (prop_ext (fun h4 : (term145 r) = r => @lem1299373 P r h1 h2 h3 h4) (fun h4 : term912 P r => @lem1298332 r h2)). Qed.
Lemma lem1299375 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) : term912 P r.
Proof. exact (EQ_MP (@lem1299374 P r h1 h2 h3) (@lem1298332 r h2)). Qed.
Lemma lem1299376 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) : term385 P.
Proof. exact (ex_intro (term913 P) (mk_nadd r) (@lem1299375 P r h1 h2 h3)). Qed.
Lemma lem1299377 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) : (term438 r) = (term385 P).
Proof. exact (prop_ext (fun h4 : term438 r => @lem1299376 P r h1 h2 h3) (fun h4 : term385 P => @lem1297728 r h2)). Qed.
Lemma lem1299378 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term438 r) (h3 : term391 P r) : term385 P.
Proof. exact (EQ_MP (@lem1299377 P r h1 h2 h3) (@lem1297728 r h2)). Qed.
Lemma lem1299379 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term391 P r) : (term438 r) = (term385 P).
Proof. exact (prop_ext (fun h3 : term438 r => @lem1299378 P r h1 h3 h2) (fun h3 : term385 P => @lem1297982 P r h1 h2)). Qed.
Lemma lem1299380 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) (h2 : term391 P r) : term385 P.
Proof. exact (EQ_MP (@lem1299379 P r h1 h2) (@lem1297982 P r h1 h2)). Qed.
Lemma lem1299381 (P : nadd -> Prop) (r : nat -> nat) (h1 : term422 P r) : term425 r P.
Proof. exact (fun h0 : term391 P r => @lem1299380 P r h1 h0). Qed.
Lemma lem1299382 (r : nat -> nat) (P : nadd -> Prop) : term427 r P.
Proof. exact (fun h0 : term422 P r => @lem1299381 P r h0). Qed.
Lemma lem1299383 (r : nat -> nat) (P : nadd -> Prop) : term426 r P.
Proof. exact (EQ_MP (@lem1297712 r P) (@lem1299382 r P)). Qed.
Lemma lem1299384 (P : nadd -> Prop) (r : nat -> nat) (h1 : term392 P r) : term425 r P.
Proof. exact (@lem1299383 r P (@lem1297608 P r h1)). Qed.
Lemma lem1299385 (r : nat -> nat) (P : nadd -> Prop) : term914 r P.
Proof. exact (fun h0 : term392 P r => @lem1299384 P r h0). Qed.
Lemma lem1299386 (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term425 r P.
Proof. exact (@lem1299385 r P (@lem1297600 P r h1)). Qed.
Lemma lem1299387 (P : nadd -> Prop) (r : nat -> nat) (h1 : term379 P r) : term385 P.
Proof. exact (@lem1299386 P r h1 (@lem1297599 P r h1)). Qed.
Lemma lem1299388 (P : nadd -> Prop) (h1 : term382 P) : term385 P.
Proof. exact (ex_elim (@lem1297592 P h1) (fun r : nat -> nat => fun h0 : term381 P r => @lem1299387 P r h0)). Qed.
Lemma lem1299389 (P : nadd -> Prop) : term387 P.
Proof. exact (fun h0 : term382 P => @lem1299388 P h0). Qed.
Lemma lem1299390 (P : nadd -> Prop) : term386 P.
Proof. exact (EQ_MP (@lem1297591 P) (@lem1299389 P)). Qed.
Lemma lem1299391 (P : nadd -> Prop) (h1 : term284 P) : term385 P.
Proof. exact (@lem1299390 P (@lem1297274 P h1)). Qed.
Lemma lem1299392 (m : nadd) (P : nadd -> Prop) (a : nadd) (h1 : term282 P m) (h2 : P a) : (term284 P) = (term385 P).
Proof. exact (prop_ext (fun h3 : term284 P => @lem1299391 P h3) (fun h3 : term385 P => @lem1297530 m P a h1 h2)). Qed.
Lemma lem1299393 (m : nadd) (P : nadd -> Prop) (a : nadd) (h1 : term282 P m) (h2 : P a) : term385 P.
Proof. exact (EQ_MP (@lem1299392 m P a h1 h2) (@lem1297530 m P a h1 h2)). Qed.
Lemma lem1299394 (P : nadd -> Prop) (h1 : term280 P) : term281 P.
Proof. exact (proj2 (@lem1297269 P h1)). Qed.
Lemma lem1299395 (P : nadd -> Prop) (h1 : term280 P) : term283 P.
Proof. exact (proj1 (@lem1297269 P h1)). Qed.
Lemma lem1299396 (P : nadd -> Prop) (a : nadd) (h1 : term281 P) (h2 : P a) : term385 P.
Proof. exact (ex_elim (@lem1297270 P h1) (fun m : nadd => fun h0 : term915 P m => @lem1299393 m P a h0 h2)). Qed.
Lemma lem1299397 (P : nadd -> Prop) (h1 : term281 P) (h2 : term283 P) : term385 P.
Proof. exact (ex_elim (@lem1297272 P h2) (fun a : nadd => fun h0 : term916 P a => @lem1299396 P a h1 h0)). Qed.
Lemma lem1299398 (P : nadd -> Prop) (h1 : term283 P) (h2 : term280 P) : (term281 P) = (term385 P).
Proof. exact (prop_ext (fun h3 : term281 P => @lem1299397 P h3 h1) (fun h3 : term385 P => @lem1299394 P h2)). Qed.
Lemma lem1299399 (P : nadd -> Prop) (h1 : term283 P) (h2 : term280 P) : term385 P.
Proof. exact (EQ_MP (@lem1299398 P h1 h2) (@lem1299394 P h2)). Qed.
Lemma lem1299400 (P : nadd -> Prop) (h1 : term280 P) : (term283 P) = (term385 P).
Proof. exact (prop_ext (fun h2 : term283 P => @lem1299399 P h2 h1) (fun h2 : term385 P => @lem1299395 P h1)). Qed.
Lemma lem1299401 (P : nadd -> Prop) (h1 : term280 P) : term385 P.
Proof. exact (EQ_MP (@lem1299400 P h1) (@lem1299395 P h1)). Qed.
Lemma lem1299402 (P : nadd -> Prop) : term917 P.
Proof. exact (fun h0 : term280 P => @lem1299401 P h0). Qed.
Lemma lem1299407 : term918.
Proof. exact (fun P : nadd -> Prop => @lem1299402 P). Qed.
