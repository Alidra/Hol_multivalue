Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LNEG_term_abbrevs.
Require Import thm0_spec.
Require Import thm1338238_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1339889_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Lemma lem1362042 (x : real) : term0 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1362043 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1362044 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1362043 x) (@lem1362042 x)). Qed.
Lemma lem1362045 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1362044 x y). Qed.
Lemma lem1362046 (y : real) (x : real) : (term2 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1362055 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1362046 y x) (@lem1362045 x y)). Qed.
Lemma lem1362056 (x : real) : (term3 x) = (term4 x).
Proof. exact (@lem1362055 x term5). Qed.
Lemma lem1362057 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362058 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1362057) (@lem1362056 x)). Qed.
Lemma lem1362059 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1362060 (x : real) : ((term3 x) = x) = ((term4 x) = x).
Proof. exact (MK_COMB (@lem1362058 x) (@lem1362059 x)). Qed.
Lemma lem1362061 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1362060 x)). Qed.
Lemma lem1362062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362063 : term10 = term11.
Proof. exact (MK_COMB (@lem1362062) (@lem1362061)). Qed.
Lemma lem1362064 : term11.
Proof. exact (EQ_MP (@lem1362063) (@lem1338512)). Qed.
Lemma lem1362065 (x : real) : term12 x.
Proof. exact (@lem1362064 x). Qed.
Lemma lem1362066 (x : real) : (term12 x) = ((term4 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1362068 (x : real) : term13 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1362069 (x : real) : (term13 x) = ((term3 x) = x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1362071 (x : real) : term14 x.
Proof. exact (@lem1338438 x). Qed.
Lemma lem1362072 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1362073 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1362072 x) (@lem1362071 x)). Qed.
Lemma lem1362074 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1362073 x y). Qed.
Lemma lem1362075 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1362076 (x : real) (y : real) : term17 x y.
Proof. exact (EQ_MP (@lem1362075 x y) (@lem1362074 x y)). Qed.
Lemma lem1362077 (x : real) (y : real) (z : real) : term18 x y z.
Proof. exact (@lem1362076 x y z). Qed.
Lemma lem1362078 (x : real) (y : real) (z : real) : (term18 x y z) = ((term19 x y z) = (term20 x y z)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1362080 (x : real) : term21 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1362081 (x : real) : (term21 x) = ((term22 x) = term5).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1362083 (x : real) : term0 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1362084 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1362085 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1362084 x) (@lem1362083 x)). Qed.
Lemma lem1362086 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1362085 x y). Qed.
Lemma lem1362087 (y : real) (x : real) : (term2 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1362096 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1362087 y x) (@lem1362086 x y)). Qed.
Lemma lem1362097 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1362096 x (real_neg x)). Qed.
Lemma lem1362098 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362099 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1362098) (@lem1362097 x)). Qed.
Lemma lem1362100 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1362101 (x : real) : ((term22 x) = term5) = ((term23 x) = term5).
Proof. exact (MK_COMB (@lem1362099 x) (@lem1362100)). Qed.
Lemma lem1362102 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1362101 x)). Qed.
Lemma lem1362103 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1362104 : term28 = term29.
Proof. exact (MK_COMB (@lem1362103) (@lem1362102)). Qed.
Lemma lem1362105 : term29.
Proof. exact (EQ_MP (@lem1362104) (@lem1338588)). Qed.
Lemma lem1362106 (x : real) : term30 x.
Proof. exact (@lem1362105 x). Qed.
Lemma lem1362107 (x : real) : (term30 x) = ((term23 x) = term5).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1362109 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1362110 (x : real) (h1 : term31) : term32 x.
Proof. exact (@lem1362109 h1 x). Qed.
Lemma lem1362111 (x : real) : (term32 x) = (term33 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1362112 (x : real) (h1 : term31) : term33 x.
Proof. exact (EQ_MP (@lem1362111 x) (@lem1362110 x h1)). Qed.
Lemma lem1362113 (x : real) (y : real) (h1 : term31) : term34 x y.
Proof. exact (@lem1362112 x h1 y). Qed.
Lemma lem1362114 (y : real) (x : real) : (term34 x y) = (term35 y x).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1362115 (y : real) (x : real) (h1 : term31) : term35 y x.
Proof. exact (EQ_MP (@lem1362114 y x) (@lem1362113 x y h1)). Qed.
Lemma lem1362116 (y : real) (x : real) (z : real) (h1 : term31) : term36 y x z.
Proof. exact (@lem1362115 y x h1 z). Qed.
Lemma lem1362117 (y : real) (x : real) (z : real) : (term36 y x z) = (term37 y x z).
Proof. exact (eq_refl (term36 y x z)). Qed.
Lemma lem1362118 (y : real) (x : real) (z : real) (h1 : term31) : term37 y x z.
Proof. exact (EQ_MP (@lem1362117 y x z) (@lem1362116 y x z h1)). Qed.
Lemma lem1362119 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1362120 (x : real) (y : real) (z : real) (h1 : term31) (h2 : real_le y z) : term38 y x z.
Proof. exact (@lem1362118 y x z h1 (@lem1362119 y z h2)). Qed.
Lemma lem1362121 (y : real) (z : real) (h1 : term31) (h2 : real_le y z) : term39 y z.
Proof. exact (fun x : real => @lem1362120 x y z h1 h2). Qed.
Lemma lem1362122 (y : real) (z : real) (h1 : term31) : term40 y z.
Proof. exact (fun h0 : real_le y z => @lem1362121 y z h1 h0). Qed.
Lemma lem1362123 (y : real) (h1 : term31) : term41 y.
Proof. exact (fun z : real => @lem1362122 y z h1). Qed.
Lemma lem1362124 (h1 : term31) : term42.
Proof. exact (fun y : real => @lem1362123 y h1). Qed.
Lemma lem1362125 : term43.
Proof. exact (fun h0 : term31 => @lem1362124 h0). Qed.
Lemma lem1362126 : term42.
Proof. exact (@lem1362125 (@lem1339889)). Qed.
Lemma lem1362127 (y : real) : term44 y.
Proof. exact (@lem1362126 y). Qed.
Lemma lem1362128 (y : real) : (term44 y) = (term41 y).
Proof. exact (eq_refl (term44 y)). Qed.
Lemma lem1362129 (y : real) : term41 y.
Proof. exact (EQ_MP (@lem1362128 y) (@lem1362127 y)). Qed.
Lemma lem1362130 (y : real) (z : real) : term45 y z.
Proof. exact (@lem1362129 y z). Qed.
Lemma lem1362131 (y : real) (z : real) : (term45 y z) = (term40 y z).
Proof. exact (eq_refl (term45 y z)). Qed.
Lemma lem1362133 (x : real) (y : real) (h1 : term46 x y) : term46 x y.
Proof. exact (h1). Qed.
Lemma lem1362135 (y : real) (z : real) : term40 y z.
Proof. exact (EQ_MP (@lem1362131 y z) (@lem1362130 y z)). Qed.
Lemma lem1362136 (x : real) (y : real) : term47 x y.
Proof. exact (@lem1362135 (real_neg x) y). Qed.
Lemma lem1362137 (x : real) (y : real) (h1 : term46 x y) : term48 x y.
Proof. exact (@lem1362136 x y (@lem1362133 x y h1)). Qed.
Lemma lem1362138 (x : real) (y : real) (h1 : term49 x y) : term49 x y.
Proof. exact (h1). Qed.
Lemma lem1362140 (y : real) (z : real) : term40 y z.
Proof. exact (EQ_MP (@lem1362131 y z) (@lem1362130 y z)). Qed.
Lemma lem1362141 (x : real) (y : real) : term50 x y.
Proof. exact (@lem1362140 term5 (real_add x y)). Qed.
Lemma lem1362142 (x : real) (y : real) (h1 : term49 x y) : term51 x y.
Proof. exact (@lem1362141 x y (@lem1362138 x y h1)). Qed.
Lemma lem1362143 (x : real) (y : real) (h1 : term48 x y) : term48 x y.
Proof. exact (h1). Qed.
Lemma lem1362144 (x : real) (y : real) (h1 : term48 x y) : term52 y x.
Proof. exact (@lem1362143 x y h1 x). Qed.
Lemma lem1362145 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (eq_refl (term52 y x)). Qed.
Lemma lem1362146 (x : real) (y : real) (h1 : term48 x y) : term53 x y.
Proof. exact (EQ_MP (@lem1362145 x y) (@lem1362144 x y h1)). Qed.
Lemma lem1362150 (x : real) : (term23 x) = term5.
Proof. exact (EQ_MP (@lem1362107 x) (@lem1362106 x)). Qed.
Lemma lem1362151 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362152 (x : real) : (term54 x) = term55.
Proof. exact (MK_COMB (@lem1362151) (@lem1362150 x)). Qed.
Lemma lem1362153 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (eq_refl (real_add x y)). Qed.
Lemma lem1362154 (x : real) (y : real) : (term53 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1362152 x) (@lem1362153 x y)). Qed.
Lemma lem1362155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362156 (x : real) (y : real) : (term56 x y) = (term57 x y).
Proof. exact (MK_COMB (@lem1362155) (@lem1362154 x y)). Qed.
Lemma lem1362157 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1362158 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1362156 x y) (@lem1362157 x y)). Qed.
Lemma lem1362160 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1362161 (x : real) (y : real) : (term59 x y) = True.
Proof. exact (@lem1362160 (term49 x y)). Qed.
Lemma lem1362162 (x : real) (y : real) : (term58 x y) = True.
Proof. exact (TRANS (@lem1362158 x y) (@lem1362161 x y)). Qed.
Lemma lem1362163 (x : real) (y : real) : True = (term58 x y).
Proof. exact (SYM (@lem1362162 x y)). Qed.
Lemma lem1362164 (x : real) (y : real) : term58 x y.
Proof. exact (EQ_MP (@lem1362163 x y) (@lem0)). Qed.
Lemma lem1362165 (x : real) (y : real) (h1 : term48 x y) : term49 x y.
Proof. exact (@lem1362164 x y (@lem1362146 x y h1)). Qed.
Lemma lem1362166 (x : real) (y : real) : term60 x y.
Proof. exact (fun h0 : term48 x y => @lem1362165 x y h0). Qed.
Lemma lem1362167 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1362168 (x : real) (y : real) (h1 : term51 x y) : term61 y x.
Proof. exact (@lem1362167 x y h1 (real_neg x)). Qed.
Lemma lem1362169 (x : real) (y : real) : (term61 y x) = (term62 x y).
Proof. exact (eq_refl (term61 y x)). Qed.
Lemma lem1362170 (x : real) (y : real) (h1 : term51 x y) : term62 x y.
Proof. exact (EQ_MP (@lem1362169 x y) (@lem1362168 x y h1)). Qed.
Lemma lem1362176 (x : real) : (term4 x) = x.
Proof. exact (EQ_MP (@lem1362066 x) (@lem1362065 x)). Qed.
Lemma lem1362177 (x : real) : (term63 x) = (real_neg x).
Proof. exact (@lem1362176 (real_neg x)). Qed.
Lemma lem1362178 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1362179 (x : real) : (term64 x) = (term65 x).
Proof. exact (MK_COMB (@lem1362178) (@lem1362177 x)). Qed.
Lemma lem1362183 (x : real) (y : real) (z : real) : (term19 x y z) = (term20 x y z).
Proof. exact (EQ_MP (@lem1362078 x y z) (@lem1362077 x y z)). Qed.
Lemma lem1362184 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem1362183 (real_neg x) x y). Qed.
Lemma lem1362186 (x : real) : (term22 x) = term5.
Proof. exact (EQ_MP (@lem1362081 x) (@lem1362080 x)). Qed.
Lemma lem1362187 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1362188 (x : real) : (term68 x) = term69.
Proof. exact (MK_COMB (@lem1362187) (@lem1362186 x)). Qed.
Lemma lem1362189 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1362190 (x : real) (y : real) : (term67 x y) = (term3 y).
Proof. exact (MK_COMB (@lem1362188 x) (@lem1362189 y)). Qed.
Lemma lem1362192 (x : real) : (term3 x) = x.
Proof. exact (EQ_MP (@lem1362069 x) (@lem1362068 x)). Qed.
Lemma lem1362193 (y : real) : (term3 y) = y.
Proof. exact (@lem1362192 y). Qed.
Lemma lem1362194 (x : real) (y : real) : (term67 x y) = y.
Proof. exact (TRANS (@lem1362190 x y) (@lem1362193 y)). Qed.
Lemma lem1362195 (x : real) (y : real) : (term66 x y) = y.
Proof. exact (TRANS (@lem1362184 x y) (@lem1362194 x y)). Qed.
Lemma lem1362196 (x : real) (y : real) : (term62 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1362179 x) (@lem1362195 x y)). Qed.
Lemma lem1362197 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362198 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1362197) (@lem1362196 x y)). Qed.
Lemma lem1362199 (x : real) (y : real) : (term46 x y) = (term46 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1362200 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1362198 x y) (@lem1362199 x y)). Qed.
Lemma lem1362202 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1362203 (x : real) (y : real) : (term73 x y) = True.
Proof. exact (@lem1362202 (term46 x y)). Qed.
Lemma lem1362204 (x : real) (y : real) : (term72 x y) = True.
Proof. exact (TRANS (@lem1362200 x y) (@lem1362203 x y)). Qed.
Lemma lem1362205 (x : real) (y : real) : True = (term72 x y).
Proof. exact (SYM (@lem1362204 x y)). Qed.
Lemma lem1362206 (x : real) (y : real) : term72 x y.
Proof. exact (EQ_MP (@lem1362205 x y) (@lem0)). Qed.
Lemma lem1362207 (x : real) (y : real) (h1 : term51 x y) : term46 x y.
Proof. exact (@lem1362206 x y (@lem1362170 x y h1)). Qed.
Lemma lem1362208 (x : real) (y : real) : term74 x y.
Proof. exact (fun h0 : term51 x y => @lem1362207 x y h0). Qed.
Lemma lem1362209 (x : real) (y : real) (h1 : term49 x y) : term46 x y.
Proof. exact (@lem1362208 x y (@lem1362142 x y h1)). Qed.
Lemma lem1362210 (x : real) (y : real) : term75 x y.
Proof. exact (fun h0 : term49 x y => @lem1362209 x y h0). Qed.
Lemma lem1362211 (x : real) (y : real) (h1 : term46 x y) : term49 x y.
Proof. exact (@lem1362166 x y (@lem1362137 x y h1)). Qed.
Lemma lem1362212 (x : real) (y : real) : term76 x y.
Proof. exact (fun h0 : term46 x y => @lem1362211 x y h0). Qed.
Lemma lem1362213 (x : real) (y : real) : term77 x y.
Proof. exact (conj (@lem1362212 x y) (@lem1362210 x y)). Qed.
Lemma lem1362214 (x : real) (y : real) : (term77 x y) = ((term46 x y) = (term49 x y)).
Proof. exact (@lem32 (term46 x y) (term49 x y)). Qed.
Lemma lem1362215 (x : real) (y : real) : (term46 x y) = (term49 x y).
Proof. exact (EQ_MP (@lem1362214 x y) (@lem1362213 x y)). Qed.
Lemma lem1362220 (x : real) : term78 x.
Proof. exact (fun y : real => @lem1362215 x y). Qed.
Lemma lem1362225 : term79.
Proof. exact (fun x : real => @lem1362220 x). Qed.
