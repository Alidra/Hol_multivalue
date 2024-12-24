Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LADD_IMP_term_abbrevs.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm10568_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1339889_spec.
Require Import thm1823_spec.
Lemma lem1487145 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1487146 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1487148 (x : real) : term2 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1487149 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1487151 (x : real) : term5 x.
Proof. exact (@lem1338438 x). Qed.
Lemma lem1487152 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1487153 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1487152 x) (@lem1487151 x)). Qed.
Lemma lem1487154 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1487153 x y). Qed.
Lemma lem1487155 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1487156 (x : real) (y : real) : term8 x y.
Proof. exact (EQ_MP (@lem1487155 x y) (@lem1487154 x y)). Qed.
Lemma lem1487157 (x : real) (y : real) (z : real) : term9 x y z.
Proof. exact (@lem1487156 x y z). Qed.
Lemma lem1487158 (x : real) (y : real) (z : real) : (term9 x y z) = ((term10 x y z) = (term11 x y z)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1487160 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1487161 (x : real) (h1 : term12) : term13 x.
Proof. exact (@lem1487160 h1 x). Qed.
Lemma lem1487162 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1487163 (x : real) (h1 : term12) : term14 x.
Proof. exact (EQ_MP (@lem1487162 x) (@lem1487161 x h1)). Qed.
Lemma lem1487164 (x : real) (y : real) (h1 : term12) : term15 x y.
Proof. exact (@lem1487163 x h1 y). Qed.
Lemma lem1487165 (y : real) (x : real) : (term15 x y) = (term16 y x).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1487166 (y : real) (x : real) (h1 : term12) : term16 y x.
Proof. exact (EQ_MP (@lem1487165 y x) (@lem1487164 x y h1)). Qed.
Lemma lem1487167 (y : real) (x : real) (z : real) (h1 : term12) : term17 y x z.
Proof. exact (@lem1487166 y x h1 z). Qed.
Lemma lem1487168 (y : real) (x : real) (z : real) : (term17 y x z) = (term18 y x z).
Proof. exact (eq_refl (term17 y x z)). Qed.
Lemma lem1487169 (y : real) (x : real) (z : real) (h1 : term12) : term18 y x z.
Proof. exact (EQ_MP (@lem1487168 y x z) (@lem1487167 y x z h1)). Qed.
Lemma lem1487170 (y : real) (z : real) (h1 : real_le y z) : real_le y z.
Proof. exact (h1). Qed.
Lemma lem1487171 (x : real) (y : real) (z : real) (h1 : term12) (h2 : real_le y z) : term19 y x z.
Proof. exact (@lem1487169 y x z h1 (@lem1487170 y z h2)). Qed.
Lemma lem1487172 (y : real) (z : real) (h1 : term12) (h2 : real_le y z) : term20 y z.
Proof. exact (fun x : real => @lem1487171 x y z h1 h2). Qed.
Lemma lem1487173 (y : real) (z : real) (h1 : term12) : term21 y z.
Proof. exact (fun h0 : real_le y z => @lem1487172 y z h1 h0). Qed.
Lemma lem1487174 (y : real) (h1 : term12) : term22 y.
Proof. exact (fun z : real => @lem1487173 y z h1). Qed.
Lemma lem1487175 (h1 : term12) : term23.
Proof. exact (fun y : real => @lem1487174 y h1). Qed.
Lemma lem1487176 : term24.
Proof. exact (fun h0 : term12 => @lem1487175 h0). Qed.
Lemma lem1487177 : term23.
Proof. exact (@lem1487176 (@lem1339889)). Qed.
Lemma lem1487178 (y : real) : term25 y.
Proof. exact (@lem1487177 y). Qed.
Lemma lem1487179 (y : real) : (term25 y) = (term22 y).
Proof. exact (eq_refl (term25 y)). Qed.
Lemma lem1487180 (y : real) : term22 y.
Proof. exact (EQ_MP (@lem1487179 y) (@lem1487178 y)). Qed.
Lemma lem1487181 (y : real) (z : real) : term26 y z.
Proof. exact (@lem1487180 y z). Qed.
Lemma lem1487182 (y : real) (z : real) : (term26 y z) = (term21 y z).
Proof. exact (eq_refl (term26 y z)). Qed.
Lemma lem1487184 (y : real) : term27 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1487185 (y : real) : (term27 y) = (term28 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1487186 (y : real) : term28 y.
Proof. exact (EQ_MP (@lem1487185 y) (@lem1487184 y)). Qed.
Lemma lem1487187 (y : real) (x : real) : term29 y x.
Proof. exact (@lem1487186 y x). Qed.
Lemma lem1487188 (y : real) (x : real) : (term29 y x) = ((real_lt x y) = (term30 y x)).
Proof. exact (eq_refl (term29 y x)). Qed.
Lemma lem1487190 (x : real) (y : real) (z : real) : (term31 y x z) = (term32 x y z).
Proof. exact (@lem10568 (term33 y x z) (real_lt y z)). Qed.
Lemma lem1487191 (y : real) (x : real) (z : real) : (term32 x y z) = (term31 y x z).
Proof. exact (SYM (@lem1487190 x y z)). Qed.
Lemma lem1487195 (y : real) (x : real) : (real_lt x y) = (term30 y x).
Proof. exact (EQ_MP (@lem1487188 y x) (@lem1487187 y x)). Qed.
Lemma lem1487196 (z : real) (x : real) (y : real) : (term33 y x z) = (term34 z x y).
Proof. exact (@lem1487195 (real_add x z) (real_add x y)). Qed.
Lemma lem1487197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487198 (z : real) (x : real) (y : real) : (term35 y x z) = (term36 z x y).
Proof. exact (MK_COMB (@lem1487197) (@lem1487196 z x y)). Qed.
Lemma lem1487200 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1487201 (z : real) (x : real) (y : real) : (term36 z x y) = (term19 z x y).
Proof. exact (@lem1487200 (term19 z x y)). Qed.
Lemma lem1487202 (z : real) (x : real) (y : real) : (term35 y x z) = (term19 z x y).
Proof. exact (TRANS (@lem1487198 z x y) (@lem1487201 z x y)). Qed.
Lemma lem1487203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1487204 (z : real) (x : real) (y : real) : (term38 y x z) = (term39 z x y).
Proof. exact (MK_COMB (@lem1487203) (@lem1487202 z x y)). Qed.
Lemma lem1487206 (y : real) (x : real) : (real_lt x y) = (term30 y x).
Proof. exact (EQ_MP (@lem1487188 y x) (@lem1487187 y x)). Qed.
Lemma lem1487207 (z : real) (y : real) : (real_lt y z) = (term30 z y).
Proof. exact (@lem1487206 z y). Qed.
Lemma lem1487208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1487209 (z : real) (y : real) : (term40 y z) = (term41 z y).
Proof. exact (MK_COMB (@lem1487208) (@lem1487207 z y)). Qed.
Lemma lem1487211 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem1487212 (z : real) (y : real) : (term41 z y) = (real_le z y).
Proof. exact (@lem1487211 (real_le z y)). Qed.
Lemma lem1487213 (z : real) (y : real) : (term40 y z) = (real_le z y).
Proof. exact (TRANS (@lem1487209 z y) (@lem1487212 z y)). Qed.
Lemma lem1487214 (x : real) (z : real) (y : real) : (term32 x y z) = (term42 x z y).
Proof. exact (MK_COMB (@lem1487204 z x y) (@lem1487213 z y)). Qed.
Lemma lem1487217 (x : real) (y : real) (z : real) : (term42 x z y) = (term32 x y z).
Proof. exact (SYM (@lem1487214 x z y)). Qed.
Lemma lem1487218 (z : real) (x : real) (y : real) (h1 : term19 z x y) : term19 z x y.
Proof. exact (h1). Qed.
Lemma lem1487220 (y : real) (z : real) : term21 y z.
Proof. exact (EQ_MP (@lem1487182 y z) (@lem1487181 y z)). Qed.
Lemma lem1487221 (z : real) (x : real) (y : real) : term43 z x y.
Proof. exact (@lem1487220 (real_add x z) (real_add x y)). Qed.
Lemma lem1487222 (z : real) (x : real) (y : real) (h1 : term19 z x y) : term44 z x y.
Proof. exact (@lem1487221 z x y (@lem1487218 z x y h1)). Qed.
Lemma lem1487223 (z : real) (x : real) (y : real) (h1 : term44 z x y) : term44 z x y.
Proof. exact (h1). Qed.
Lemma lem1487224 (z : real) (x : real) (y : real) (h1 : term44 z x y) : term45 z y x.
Proof. exact (@lem1487223 z x y h1 (real_neg x)). Qed.
Lemma lem1487225 (z : real) (x : real) (y : real) : (term45 z y x) = (term46 z x y).
Proof. exact (eq_refl (term45 z y x)). Qed.
Lemma lem1487226 (z : real) (x : real) (y : real) (h1 : term44 z x y) : term46 z x y.
Proof. exact (EQ_MP (@lem1487225 z x y) (@lem1487224 z x y h1)). Qed.
Lemma lem1487232 (x : real) (y : real) (z : real) : (term10 x y z) = (term11 x y z).
Proof. exact (EQ_MP (@lem1487158 x y z) (@lem1487157 x y z)). Qed.
Lemma lem1487233 (x : real) (z : real) : (term47 x z) = (term48 x z).
Proof. exact (@lem1487232 (real_neg x) x z). Qed.
Lemma lem1487235 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1487149 x) (@lem1487148 x)). Qed.
Lemma lem1487236 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1487237 (x : real) : (term49 x) = term50.
Proof. exact (MK_COMB (@lem1487236) (@lem1487235 x)). Qed.
Lemma lem1487238 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1487239 (x : real) (z : real) : (term48 x z) = (term1 z).
Proof. exact (MK_COMB (@lem1487237 x) (@lem1487238 z)). Qed.
Lemma lem1487241 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1487146 x) (@lem1487145 x)). Qed.
Lemma lem1487242 (z : real) : (term1 z) = z.
Proof. exact (@lem1487241 z). Qed.
Lemma lem1487243 (x : real) (z : real) : (term48 x z) = z.
Proof. exact (TRANS (@lem1487239 x z) (@lem1487242 z)). Qed.
Lemma lem1487244 (x : real) (z : real) : (term47 x z) = z.
Proof. exact (TRANS (@lem1487233 x z) (@lem1487243 x z)). Qed.
Lemma lem1487245 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1487246 (x : real) (z : real) : (term51 x z) = (real_le z).
Proof. exact (MK_COMB (@lem1487245) (@lem1487244 x z)). Qed.
Lemma lem1487250 (x : real) (y : real) (z : real) : (term10 x y z) = (term11 x y z).
Proof. exact (EQ_MP (@lem1487158 x y z) (@lem1487157 x y z)). Qed.
Lemma lem1487251 (x : real) (y : real) : (term47 x y) = (term48 x y).
Proof. exact (@lem1487250 (real_neg x) x y). Qed.
Lemma lem1487253 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1487149 x) (@lem1487148 x)). Qed.
Lemma lem1487254 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1487255 (x : real) : (term49 x) = term50.
Proof. exact (MK_COMB (@lem1487254) (@lem1487253 x)). Qed.
Lemma lem1487256 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1487257 (x : real) (y : real) : (term48 x y) = (term1 y).
Proof. exact (MK_COMB (@lem1487255 x) (@lem1487256 y)). Qed.
Lemma lem1487259 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1487146 x) (@lem1487145 x)). Qed.
Lemma lem1487260 (y : real) : (term1 y) = y.
Proof. exact (@lem1487259 y). Qed.
Lemma lem1487261 (x : real) (y : real) : (term48 x y) = y.
Proof. exact (TRANS (@lem1487257 x y) (@lem1487260 y)). Qed.
Lemma lem1487262 (x : real) (y : real) : (term47 x y) = y.
Proof. exact (TRANS (@lem1487251 x y) (@lem1487261 x y)). Qed.
Lemma lem1487263 (x : real) (z : real) (y : real) : (term46 z x y) = (real_le z y).
Proof. exact (MK_COMB (@lem1487246 x z) (@lem1487262 x y)). Qed.
Lemma lem1487264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1487265 (x : real) (z : real) (y : real) : (term52 z x y) = (term53 z y).
Proof. exact (MK_COMB (@lem1487264) (@lem1487263 x z y)). Qed.
Lemma lem1487266 (z : real) (y : real) : (real_le z y) = (real_le z y).
Proof. exact (eq_refl (real_le z y)). Qed.
Lemma lem1487267 (x : real) (z : real) (y : real) : (term54 x z y) = (term55 z y).
Proof. exact (MK_COMB (@lem1487265 x z y) (@lem1487266 z y)). Qed.
Lemma lem1487269 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1487270 (z : real) (y : real) : (term55 z y) = True.
Proof. exact (@lem1487269 (real_le z y)). Qed.
Lemma lem1487271 (x : real) (z : real) (y : real) : (term54 x z y) = True.
Proof. exact (TRANS (@lem1487267 x z y) (@lem1487270 z y)). Qed.
Lemma lem1487272 (x : real) (z : real) (y : real) : True = (term54 x z y).
Proof. exact (SYM (@lem1487271 x z y)). Qed.
Lemma lem1487273 (x : real) (z : real) (y : real) : term54 x z y.
Proof. exact (EQ_MP (@lem1487272 x z y) (@lem0)). Qed.
Lemma lem1487274 (z : real) (x : real) (y : real) (h1 : term44 z x y) : real_le z y.
Proof. exact (@lem1487273 x z y (@lem1487226 z x y h1)). Qed.
Lemma lem1487275 (x : real) (z : real) (y : real) : term56 x z y.
Proof. exact (fun h0 : term44 z x y => @lem1487274 z x y h0). Qed.
Lemma lem1487276 (z : real) (x : real) (y : real) (h1 : term19 z x y) : real_le z y.
Proof. exact (@lem1487275 x z y (@lem1487222 z x y h1)). Qed.
Lemma lem1487277 (x : real) (z : real) (y : real) : term42 x z y.
Proof. exact (fun h0 : term19 z x y => @lem1487276 z x y h0). Qed.
Lemma lem1487278 (x : real) (y : real) (z : real) : term32 x y z.
Proof. exact (EQ_MP (@lem1487217 x y z) (@lem1487277 x z y)). Qed.
Lemma lem1487279 (y : real) (x : real) (z : real) : term31 y x z.
Proof. exact (EQ_MP (@lem1487191 y x z) (@lem1487278 x y z)). Qed.
Lemma lem1487284 (y : real) (x : real) : term57 y x.
Proof. exact (fun z : real => @lem1487279 y x z). Qed.
Lemma lem1487289 (x : real) : term58 x.
Proof. exact (fun y : real => @lem1487284 y x). Qed.
Lemma lem1487294 : term59.
Proof. exact (fun x : real => @lem1487289 x). Qed.
