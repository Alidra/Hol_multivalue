Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNIQUE_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import EXISTS_REFL_spec.
Require Import EXISTS_UNIQUE_ALT_spec.
Require Import FORALL_AND_THM_spec.
Require Import LEFT_FORALL_IMP_THM_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm4211_spec.
Require Import thm43_spec.
Require Import thm554_spec.
Require Import thm555_spec.
Require Import thm7_spec.
Lemma lem8071 {A : Type'} (a : A) : term0 A a.
Proof. exact (@lem4363 A a). Qed.
Lemma lem8072 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (eq_refl (term0 A a)). Qed.
Lemma lem8073 {A : Type'} (a : A) : term1 A a.
Proof. exact (EQ_MP (@lem8072 A a) (@lem8071 A a)). Qed.
Lemma lem8074 {A : Type'} (a : A) : (term1 A a) = ((term1 A a) = True).
Proof. exact (@lem7 (term1 A a)). Qed.
Lemma lem8076 {A : Type'} (P : A -> Prop) : term2 A P.
Proof. exact (@lem6754 A P). Qed.
Lemma lem8077 {A : Type'} (P : A -> Prop) : (term2 A P) = (term3 A P).
Proof. exact (eq_refl (term2 A P)). Qed.
Lemma lem8078 {A : Type'} (P : A -> Prop) : term3 A P.
Proof. exact (EQ_MP (@lem8077 A P) (@lem8076 A P)). Qed.
Lemma lem8079 {A : Type'} (P : A -> Prop) (Q : Prop) : term4 A P Q.
Proof. exact (@lem8078 A P Q). Qed.
Lemma lem8080 {A : Type'} (P : A -> Prop) (Q : Prop) : (term4 A P Q) = ((term5 A P Q) = (term6 A P Q)).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem8082 {A : Type'} (P : A -> Prop) : term7 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem8083 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem8084 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (EQ_MP (@lem8083 A P) (@lem8082 A P)). Qed.
Lemma lem8085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term9 A P Q.
Proof. exact (@lem8084 A P Q). Qed.
Lemma lem8086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term9 A P Q) = ((term10 A P Q) = (term11 A P Q)).
Proof. exact (eq_refl (term9 A P Q)). Qed.
Lemma lem8088 {A : Type'} (x : A) : term12 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem8089 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem8090 {A : Type'} (x : A) : term13 A x.
Proof. exact (EQ_MP (@lem8089 A x) (@lem8088 A x)). Qed.
Lemma lem8091 {A : Type'} (x : A) (y : A) : term14 A x y.
Proof. exact (@lem8090 A x y). Qed.
Lemma lem8092 {A : Type'} (y : A) (x : A) : (term14 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term14 A x y)). Qed.
Lemma lem8138 (a : Prop) (b : Prop) (h1 : a = b) : a = b.
Proof. exact (h1). Qed.
Lemma lem8139 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem8140 (b : Prop) (a : Prop) : term15 b a.
Proof. exact (@lem43 b a). Qed.
Lemma lem8142 (a : Prop) (b : Prop) : term16 a b.
Proof. exact (@lem37 a b). Qed.
Lemma lem8145 (a : Prop) (b : Prop) (h1 : a = b) : b -> a.
Proof. exact (@lem8140 b a (@lem8138 a b h1)). Qed.
Lemma lem8146 (a : Prop) (b : Prop) (h1 : a = b) : a -> b.
Proof. exact (@lem8142 a b (@lem8138 a b h1)). Qed.
Lemma lem8148 (a : Prop) (b : Prop) (h1 : a -> b) : a -> b.
Proof. exact (h1). Qed.
Lemma lem8149 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem8150 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (@lem8148 a b h2 (@lem8149 a h1)). Qed.
Lemma lem8151 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem8150 a b h1 h2) (fun h3 : b => @lem8139 a h1)). Qed.
Lemma lem8152 (a : Prop) (b : Prop) (h1 : a) (h2 : a -> b) : b.
Proof. exact (EQ_MP (@lem8151 a b h1 h2) (@lem8139 a h1)). Qed.
Lemma lem8153 (b : Prop) (a : Prop) (h1 : a) : term17 a b.
Proof. exact (fun h0 : a -> b => @lem8152 a b h1 h0). Qed.
Lemma lem8154 (b : Prop) (a : Prop) (h1 : a) : term18 a b.
Proof. exact (fun h0 : b -> a => @lem8153 b a h1). Qed.
Lemma lem8155 (a : Prop) (b : Prop) (h1 : a) (h2 : a = b) : term17 a b.
Proof. exact (@lem8154 b a h1 (@lem8145 a b h2)). Qed.
Lemma lem8156 (a : Prop) (b : Prop) (h1 : a) (h2 : a = b) : b.
Proof. exact (@lem8155 a b h1 h2 (@lem8146 a b h2)). Qed.
Lemma lem8157 (a : Prop) (b : Prop) (h1 : a = b) : a -> b.
Proof. exact (fun h0 : a => @lem8156 a b h0 h1). Qed.
Lemma lem8158 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem8159 (b : Prop) (a : Prop) : term15 b a.
Proof. exact (@lem43 b a). Qed.
Lemma lem8161 (a : Prop) (b : Prop) : term16 a b.
Proof. exact (@lem37 a b). Qed.
Lemma lem8164 (a : Prop) (b : Prop) (h1 : a = b) : b -> a.
Proof. exact (@lem8159 b a (@lem8138 a b h1)). Qed.
Lemma lem8165 (a : Prop) (b : Prop) (h1 : a = b) : a -> b.
Proof. exact (@lem8161 a b (@lem8138 a b h1)). Qed.
Lemma lem8166 (b : Prop) (a : Prop) (h1 : b -> a) : b -> a.
Proof. exact (h1). Qed.
Lemma lem8174 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem8175 (b : Prop) (a : Prop) (h1 : b) (h2 : b -> a) : a.
Proof. exact (@lem8166 b a h2 (@lem8174 b h1)). Qed.
Lemma lem8176 (b : Prop) (a : Prop) (h1 : b) (h2 : b -> a) : b = a.
Proof. exact (prop_ext (fun h3 : b => @lem8175 b a h1 h2) (fun h3 : a => @lem8158 b h1)). Qed.
Lemma lem8177 (b : Prop) (a : Prop) (h1 : b) (h2 : b -> a) : a.
Proof. exact (EQ_MP (@lem8176 b a h1 h2) (@lem8158 b h1)). Qed.
Lemma lem8178 (b : Prop) (a : Prop) (h1 : b) (h2 : b -> a) : term19 b a.
Proof. exact (fun h0 : a -> b => @lem8177 b a h1 h2). Qed.
Lemma lem8179 (a : Prop) (b : Prop) (h1 : b) : term20 b a.
Proof. exact (fun h0 : b -> a => @lem8178 b a h1 h0). Qed.
Lemma lem8180 (a : Prop) (b : Prop) (h1 : b) (h2 : a = b) : term19 b a.
Proof. exact (@lem8179 a b h1 (@lem8164 a b h2)). Qed.
Lemma lem8181 (a : Prop) (b : Prop) (h1 : b) (h2 : a = b) : a.
Proof. exact (@lem8180 a b h1 h2 (@lem8165 a b h2)). Qed.
Lemma lem8182 (a : Prop) (b : Prop) (h1 : a = b) : b -> a.
Proof. exact (fun h0 : b => @lem8181 a b h0 h1). Qed.
Lemma lem8183 (a : Prop) (b : Prop) (h1 : a = b) : term21 b a.
Proof. exact (conj (@lem8157 a b h1) (@lem8182 a b h1)). Qed.
Lemma lem8184 (b : Prop) (a : Prop) : term22 b a.
Proof. exact (fun h0 : a = b => @lem8183 a b h0). Qed.
Lemma lem8185 (b : Prop) (a : Prop) (h1 : term21 b a) : term21 b a.
Proof. exact (h1). Qed.
Lemma lem8186 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem8188 (b : Prop) (a : Prop) (h1 : term21 b a) : a -> b.
Proof. exact (proj1 (@lem8185 b a h1)). Qed.
Lemma lem8195 (a : Prop) (h1 : a) : a.
Proof. exact (h1). Qed.
Lemma lem8196 (b : Prop) (a : Prop) (h1 : a) (h2 : term21 b a) : b.
Proof. exact (@lem8188 b a h2 (@lem8195 a h1)). Qed.
Lemma lem8197 (b : Prop) (a : Prop) (h1 : a) (h2 : term21 b a) : a = b.
Proof. exact (prop_ext (fun h3 : a => @lem8196 b a h1 h2) (fun h3 : b => @lem8186 a h1)). Qed.
Lemma lem8198 (b : Prop) (a : Prop) (h1 : a) (h2 : term21 b a) : b.
Proof. exact (EQ_MP (@lem8197 b a h1 h2) (@lem8186 a h1)). Qed.
Lemma lem8199 (b : Prop) (a : Prop) (h1 : term21 b a) : a -> b.
Proof. exact (fun h0 : a => @lem8198 b a h0 h1). Qed.
Lemma lem8200 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem8201 (b : Prop) (a : Prop) (h1 : term21 b a) : b -> a.
Proof. exact (proj2 (@lem8185 b a h1)). Qed.
Lemma lem8203 (b : Prop) (h1 : b) : b.
Proof. exact (h1). Qed.
Lemma lem8204 (b : Prop) (a : Prop) (h1 : b) (h2 : term21 b a) : a.
Proof. exact (@lem8201 b a h2 (@lem8203 b h1)). Qed.
Lemma lem8205 (b : Prop) (a : Prop) (h1 : b) (h2 : term21 b a) : b = a.
Proof. exact (prop_ext (fun h3 : b => @lem8204 b a h1 h2) (fun h3 : a => @lem8200 b h1)). Qed.
Lemma lem8206 (b : Prop) (a : Prop) (h1 : b) (h2 : term21 b a) : a.
Proof. exact (EQ_MP (@lem8205 b a h1 h2) (@lem8200 b h1)). Qed.
Lemma lem8207 (b : Prop) (a : Prop) (h1 : term21 b a) : b -> a.
Proof. exact (fun h0 : b => @lem8206 b a h0 h1). Qed.
Lemma lem8208 (b : Prop) (a : Prop) (h1 : term21 b a) : term21 b a.
Proof. exact (conj (@lem8199 b a h1) (@lem8207 b a h1)). Qed.
Lemma lem8209 (a : Prop) (b : Prop) : (term21 b a) = (a = b).
Proof. exact (@lem32 a b). Qed.
Lemma lem8210 (b : Prop) (a : Prop) (h1 : term21 b a) : a = b.
Proof. exact (EQ_MP (@lem8209 a b) (@lem8208 b a h1)). Qed.
Lemma lem8211 (a : Prop) (b : Prop) : term23 a b.
Proof. exact (fun h0 : term21 b a => @lem8210 b a h0). Qed.
Lemma lem8212 (a : Prop) (b : Prop) : term24 a b.
Proof. exact (conj (@lem8184 b a) (@lem8211 a b)). Qed.
Lemma lem8213 (b : Prop) (a : Prop) : (term24 a b) = ((a = b) = (term21 b a)).
Proof. exact (@lem32 (a = b) (term21 b a)). Qed.
Lemma lem8215 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (@lem8062 A P). Qed.
Lemma lem8216 {A : Type'} (P : A -> Prop) : (term25 A P) = ((term26 A P) = (term27 A P)).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem8221 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (EQ_MP (@lem8216 A P) (@lem8215 A P)). Qed.
Lemma lem8222 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (@lem8221 A P). Qed.
Lemma lem8235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8236 {A : Type'} (P : A -> Prop) : (term28 A P) = (term29 A P).
Proof. exact (MK_COMB (@lem8235) (@lem8222 A P)). Qed.
Lemma lem8251 {A : Type'} (P : A -> Prop) : (term30 A P) = (term30 A P).
Proof. exact (eq_refl (term30 A P)). Qed.
Lemma lem8252 {A : Type'} (P : A -> Prop) : ((term26 A P) = (term30 A P)) = ((term27 A P) = (term30 A P)).
Proof. exact (MK_COMB (@lem8236 A P) (@lem8251 A P)). Qed.
Lemma lem8255 {A : Type'} (P : A -> Prop) : ((term27 A P) = (term30 A P)) = ((term26 A P) = (term30 A P)).
Proof. exact (SYM (@lem8252 A P)). Qed.
Lemma lem8256 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8258 (b : Prop) (a : Prop) : (a = b) = (term21 b a).
Proof. exact (EQ_MP (@lem8213 b a) (@lem8212 a b)). Qed.
Lemma lem8259 {A : Type'} (x : A) (P : A -> Prop) (y : A) : ((P y) = (x = y)) = (term31 A x P y).
Proof. exact (@lem8258 (x = y) (P y)). Qed.
Lemma lem8260 {A : Type'} (x : A) (P : A -> Prop) : (term32 A P x) = (term33 A x P).
Proof. exact (fun_ext (fun y : A => @lem8259 A x P y)). Qed.
Lemma lem8261 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8262 {A : Type'} (x : A) (P : A -> Prop) : (term34 A P x) = (term35 A x P).
Proof. exact (MK_COMB (@lem8261 A) (@lem8260 A x P)). Qed.
Lemma lem8263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8264 {A : Type'} (x : A) (P : A -> Prop) : (term36 A P x) = (term37 A x P).
Proof. exact (MK_COMB (@lem8263) (@lem8262 A x P)). Qed.
Lemma lem8265 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8266 {A : Type'} (P : A -> Prop) (x : A) : ((term34 A P x) = (term38 A P x)) = ((term35 A x P) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8264 A x P) (@lem8265 A P x)). Qed.
Lemma lem8267 {A : Type'} (P : A -> Prop) (x : A) : ((term35 A x P) = (term38 A P x)) = ((term34 A P x) = (term38 A P x)).
Proof. exact (SYM (@lem8266 A P x)). Qed.
Lemma lem8269 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem8092 A y x) (@lem8091 A x y)). Qed.
Lemma lem8270 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem8269 A y x). Qed.
Lemma lem8271 {A : Type'} (P : A -> Prop) (y : A) : (term39 A P y) = (term39 A P y).
Proof. exact (eq_refl (term39 A P y)). Qed.
Lemma lem8272 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term40 A P x y) = (term41 A P y x).
Proof. exact (MK_COMB (@lem8271 A P y) (@lem8270 A y x)). Qed.
Lemma lem8273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8274 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term42 A P x y) = (term43 A P y x).
Proof. exact (MK_COMB (@lem8273) (@lem8272 A P y x)). Qed.
Lemma lem8276 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem8092 A y x) (@lem8091 A x y)). Qed.
Lemma lem8277 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem8276 A y x). Qed.
Lemma lem8278 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8279 {A : Type'} (y : A) (x : A) : (term44 A x y) = (term44 A y x).
Proof. exact (MK_COMB (@lem8278) (@lem8277 A y x)). Qed.
Lemma lem8280 {A : Type'} (P : A -> Prop) (y : A) : (P y) = (P y).
Proof. exact (eq_refl (P y)). Qed.
Lemma lem8281 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term45 A x P y) = (term46 A x P y).
Proof. exact (MK_COMB (@lem8279 A y x) (@lem8280 A P y)). Qed.
Lemma lem8282 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term31 A x P y) = (term47 A x P y).
Proof. exact (MK_COMB (@lem8274 A P y x) (@lem8281 A x P y)). Qed.
Lemma lem8283 {A : Type'} (x : A) (P : A -> Prop) : (term33 A x P) = (term48 A x P).
Proof. exact (fun_ext (fun y : A => @lem8282 A x P y)). Qed.
Lemma lem8284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8285 {A : Type'} (x : A) (P : A -> Prop) : (term35 A x P) = (term49 A x P).
Proof. exact (MK_COMB (@lem8284 A) (@lem8283 A x P)). Qed.
Lemma lem8286 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8287 {A : Type'} (x : A) (P : A -> Prop) : (term37 A x P) = (term50 A x P).
Proof. exact (MK_COMB (@lem8286) (@lem8285 A x P)). Qed.
Lemma lem8288 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8289 {A : Type'} (P : A -> Prop) (x : A) : ((term35 A x P) = (term38 A P x)) = ((term49 A x P) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8287 A x P) (@lem8288 A P x)). Qed.
Lemma lem8290 {A : Type'} (P : A -> Prop) (x : A) : ((term49 A x P) = (term38 A P x)) = ((term35 A x P) = (term38 A P x)).
Proof. exact (SYM (@lem8289 A P x)). Qed.
Lemma lem8294 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (EQ_MP (@lem8086 A P Q) (@lem8085 A P Q)). Qed.
Lemma lem8295 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term10 A P Q) = (term11 A P Q).
Proof. exact (@lem8294 A P Q). Qed.
Lemma lem8296 {A : Type'} (x : A) (P : A -> Prop) : (term51 A x P) = (term52 A x P).
Proof. exact (@lem8295 A (term53 A P x) (term54 A x P)). Qed.
Lemma lem8297 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term55 A P x y) = (term41 A P y x).
Proof. exact (eq_refl (term55 A P x y)). Qed.
Lemma lem8298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8299 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term56 A P x y) = (term43 A P y x).
Proof. exact (MK_COMB (@lem8298) (@lem8297 A P y x)). Qed.
Lemma lem8300 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term57 A x P y) = (term46 A x P y).
Proof. exact (eq_refl (term57 A x P y)). Qed.
Lemma lem8301 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term58 A x P y) = (term47 A x P y).
Proof. exact (MK_COMB (@lem8299 A P y x) (@lem8300 A x P y)). Qed.
Lemma lem8302 {A : Type'} (x : A) (P : A -> Prop) : (term59 A x P) = (term48 A x P).
Proof. exact (fun_ext (fun y : A => @lem8301 A x P y)). Qed.
Lemma lem8303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8304 {A : Type'} (x : A) (P : A -> Prop) : (term51 A x P) = (term49 A x P).
Proof. exact (MK_COMB (@lem8303 A) (@lem8302 A x P)). Qed.
Lemma lem8305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8306 {A : Type'} (x : A) (P : A -> Prop) : (term60 A x P) = (term50 A x P).
Proof. exact (MK_COMB (@lem8305) (@lem8304 A x P)). Qed.
Lemma lem8307 {A : Type'} (P : A -> Prop) (y : A) (x : A) : (term55 A P x y) = (term41 A P y x).
Proof. exact (eq_refl (term55 A P x y)). Qed.
Lemma lem8308 {A : Type'} (P : A -> Prop) (x : A) : (term61 A P x) = (term53 A P x).
Proof. exact (fun_ext (fun y : A => @lem8307 A P y x)). Qed.
Lemma lem8309 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8310 {A : Type'} (P : A -> Prop) (x : A) : (term62 A P x) = (term63 A P x).
Proof. exact (MK_COMB (@lem8309 A) (@lem8308 A P x)). Qed.
Lemma lem8311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8312 {A : Type'} (P : A -> Prop) (x : A) : (term64 A P x) = (term65 A P x).
Proof. exact (MK_COMB (@lem8311) (@lem8310 A P x)). Qed.
Lemma lem8313 {A : Type'} (x : A) (P : A -> Prop) (y : A) : (term57 A x P y) = (term46 A x P y).
Proof. exact (eq_refl (term57 A x P y)). Qed.
Lemma lem8314 {A : Type'} (x : A) (P : A -> Prop) : (term66 A x P) = (term54 A x P).
Proof. exact (fun_ext (fun y : A => @lem8313 A x P y)). Qed.
Lemma lem8315 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8316 {A : Type'} (x : A) (P : A -> Prop) : (term67 A x P) = (term68 A x P).
Proof. exact (MK_COMB (@lem8315 A) (@lem8314 A x P)). Qed.
Lemma lem8317 {A : Type'} (x : A) (P : A -> Prop) : (term52 A x P) = (term69 A x P).
Proof. exact (MK_COMB (@lem8312 A P x) (@lem8316 A x P)). Qed.
Lemma lem8318 {A : Type'} (x : A) (P : A -> Prop) : ((term51 A x P) = (term52 A x P)) = ((term49 A x P) = (term69 A x P)).
Proof. exact (MK_COMB (@lem8306 A x P) (@lem8317 A x P)). Qed.
Lemma lem8319 {A : Type'} (x : A) (P : A -> Prop) : (term49 A x P) = (term69 A x P).
Proof. exact (EQ_MP (@lem8318 A x P) (@lem8296 A x P)). Qed.
Lemma lem8340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8341 {A : Type'} (x : A) (P : A -> Prop) : (term50 A x P) = (term70 A x P).
Proof. exact (MK_COMB (@lem8340) (@lem8319 A x P)). Qed.
Lemma lem8352 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8353 {A : Type'} (P : A -> Prop) (x : A) : ((term49 A x P) = (term38 A P x)) = ((term69 A x P) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8341 A x P) (@lem8352 A P x)). Qed.
Lemma lem8356 {A : Type'} (P : A -> Prop) (x : A) : ((term69 A x P) = (term38 A P x)) = ((term49 A x P) = (term38 A P x)).
Proof. exact (SYM (@lem8353 A P x)). Qed.
Lemma lem8401 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term71 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem8402 (p : Prop) (q : Prop) (p' : Prop) : term72 p q p'.
Proof. exact (fun q' : Prop => @lem8401 p q p' q'). Qed.
Lemma lem8403 (p : Prop) (q : Prop) : term73 p q.
Proof. exact (fun p' : Prop => @lem8402 p q p'). Qed.
Lemma lem8404 {A : Type'} (x : A) (P : A -> Prop) (y : A) : term74 A x P y.
Proof. exact (@lem8403 (y = x) (P y)). Qed.
Lemma lem8405 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) : term75 A x P y p'.
Proof. exact (@lem8404 A x P y p'). Qed.
Lemma lem8406 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) : (term75 A x P y p') = (term76 A x P y p').
Proof. exact (eq_refl (term75 A x P y p')). Qed.
Lemma lem8407 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) : term76 A x P y p'.
Proof. exact (EQ_MP (@lem8406 A x P y p') (@lem8405 A x P y p')). Qed.
Lemma lem8408 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) (q' : Prop) : term77 A x P y p' q'.
Proof. exact (@lem8407 A x P y p' q'). Qed.
Lemma lem8409 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) (q' : Prop) : (term77 A x P y p' q') = (term78 A x P y p' q').
Proof. exact (eq_refl (term77 A x P y p' q')). Qed.
Lemma lem8410 {A : Type'} (x : A) (P : A -> Prop) (y : A) (p' : Prop) (q' : Prop) : term78 A x P y p' q'.
Proof. exact (EQ_MP (@lem8409 A x P y p' q') (@lem8408 A x P y p' q')). Qed.
Lemma lem8413 {A : Type'} (y : A) (x : A) : (y = x) = (y = x).
Proof. exact (eq_refl (y = x)). Qed.
Lemma lem8414 {A : Type'} (P : A -> Prop) (y : A) (x : A) (q' : Prop) : term79 A P y x q'.
Proof. exact (@lem8410 A x P y (y = x) q'). Qed.
Lemma lem8415 {A : Type'} (P : A -> Prop) (y : A) (x : A) (q' : Prop) : term80 A P y x q'.
Proof. exact (@lem8414 A P y x q' (@lem8413 A y x)). Qed.
Lemma lem8418 {A : Type'} (y : A) (x : A) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem8419 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem8420 {A : Type'} (P : A -> Prop) (y : A) (x : A) (h1 : y = x) : (P y) = (P x).
Proof. exact (MK_COMB (@lem8419 A P) (@lem8418 A y x h1)). Qed.
Lemma lem8421 {A : Type'} (y : A) (P : A -> Prop) (x : A) : term81 A y P x.
Proof. exact (fun h0 : y = x => @lem8420 A P y x h0). Qed.
Lemma lem8422 {A : Type'} (y : A) (P : A -> Prop) (x : A) : term82 A y P x.
Proof. exact (@lem8415 A P y x (P x)). Qed.
Lemma lem8423 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term46 A x P y) = (term45 A y P x).
Proof. exact (@lem8422 A y P x (@lem8421 A y P x)). Qed.
Lemma lem8451 {A : Type'} (P : A -> Prop) (x : A) : (term54 A x P) = (term83 A P x).
Proof. exact (fun_ext (fun y : A => @lem8423 A y P x)). Qed.
Lemma lem8479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8480 {A : Type'} (P : A -> Prop) (x : A) : (term68 A x P) = (term84 A P x).
Proof. exact (MK_COMB (@lem8479 A) (@lem8451 A P x)). Qed.
Lemma lem8512 {A : Type'} (P : A -> Prop) (x : A) : (term65 A P x) = (term65 A P x).
Proof. exact (eq_refl (term65 A P x)). Qed.
Lemma lem8513 {A : Type'} (P : A -> Prop) (x : A) : (term69 A x P) = (term85 A P x).
Proof. exact (MK_COMB (@lem8512 A P x) (@lem8480 A P x)). Qed.
Lemma lem8578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8579 {A : Type'} (P : A -> Prop) (x : A) : (term70 A x P) = (term86 A P x).
Proof. exact (MK_COMB (@lem8578) (@lem8513 A P x)). Qed.
Lemma lem8677 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8678 {A : Type'} (P : A -> Prop) (x : A) : ((term69 A x P) = (term38 A P x)) = ((term85 A P x) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8579 A P x) (@lem8677 A P x)). Qed.
Lemma lem8778 {A : Type'} (P : A -> Prop) (x : A) : ((term85 A P x) = (term38 A P x)) = ((term69 A x P) = (term38 A P x)).
Proof. exact (SYM (@lem8678 A P x)). Qed.
Lemma lem8796 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = (term6 A P Q).
Proof. exact (EQ_MP (@lem8080 A P Q) (@lem8079 A P Q)). Qed.
Lemma lem8797 {A : Type'} (P : A -> Prop) (Q : Prop) : (term5 A P Q) = (term6 A P Q).
Proof. exact (@lem8796 A P Q). Qed.
Lemma lem8798 {A : Type'} (P : A -> Prop) (x : A) : (term87 A P x) = (term88 A P x).
Proof. exact (@lem8797 A (term89 A x) (P x)). Qed.
Lemma lem8799 {A : Type'} (y : A) (x : A) : (term90 A x y) = (y = x).
Proof. exact (eq_refl (term90 A x y)). Qed.
Lemma lem8800 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8801 {A : Type'} (y : A) (x : A) : (term91 A x y) = (term44 A y x).
Proof. exact (MK_COMB (@lem8800) (@lem8799 A y x)). Qed.
Lemma lem8802 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem8803 {A : Type'} (y : A) (P : A -> Prop) (x : A) : (term92 A y P x) = (term45 A y P x).
Proof. exact (MK_COMB (@lem8801 A y x) (@lem8802 A P x)). Qed.
Lemma lem8804 {A : Type'} (P : A -> Prop) (x : A) : (term93 A P x) = (term83 A P x).
Proof. exact (fun_ext (fun y : A => @lem8803 A y P x)). Qed.
Lemma lem8805 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem8806 {A : Type'} (P : A -> Prop) (x : A) : (term87 A P x) = (term84 A P x).
Proof. exact (MK_COMB (@lem8805 A) (@lem8804 A P x)). Qed.
Lemma lem8807 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8808 {A : Type'} (P : A -> Prop) (x : A) : (term94 A P x) = (term95 A P x).
Proof. exact (MK_COMB (@lem8807) (@lem8806 A P x)). Qed.
Lemma lem8809 {A : Type'} (y : A) (x : A) : (term90 A x y) = (y = x).
Proof. exact (eq_refl (term90 A x y)). Qed.
Lemma lem8810 {A : Type'} (x : A) : (term96 A x) = (term89 A x).
Proof. exact (fun_ext (fun y : A => @lem8809 A y x)). Qed.
Lemma lem8811 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem8812 {A : Type'} (x : A) : (term97 A x) = (term1 A x).
Proof. exact (MK_COMB (@lem8811 A) (@lem8810 A x)). Qed.
Lemma lem8813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8814 {A : Type'} (x : A) : (term98 A x) = (term99 A x).
Proof. exact (MK_COMB (@lem8813) (@lem8812 A x)). Qed.
Lemma lem8815 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem8816 {A : Type'} (P : A -> Prop) (x : A) : (term88 A P x) = (term100 A P x).
Proof. exact (MK_COMB (@lem8814 A x) (@lem8815 A P x)). Qed.
Lemma lem8817 {A : Type'} (P : A -> Prop) (x : A) : ((term87 A P x) = (term88 A P x)) = ((term84 A P x) = (term100 A P x)).
Proof. exact (MK_COMB (@lem8808 A P x) (@lem8816 A P x)). Qed.
Lemma lem8818 {A : Type'} (P : A -> Prop) (x : A) : (term84 A P x) = (term100 A P x).
Proof. exact (EQ_MP (@lem8817 A P x) (@lem8798 A P x)). Qed.
Lemma lem8822 {A : Type'} (a : A) : (term1 A a) = True.
Proof. exact (EQ_MP (@lem8074 A a) (@lem8073 A a)). Qed.
Lemma lem8823 {A : Type'} (a : A) : (term1 A a) = True.
Proof. exact (@lem8822 A a). Qed.
Lemma lem8824 {A : Type'} (x : A) : (term1 A x) = True.
Proof. exact (@lem8823 A x). Qed.
Lemma lem8825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8826 {A : Type'} (x : A) : (term99 A x) = (imp True).
Proof. exact (MK_COMB (@lem8825) (@lem8824 A x)). Qed.
Lemma lem8827 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem8828 {A : Type'} (P : A -> Prop) (x : A) : (term100 A P x) = (term101 A P x).
Proof. exact (MK_COMB (@lem8826 A x) (@lem8827 A P x)). Qed.
Lemma lem8830 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem8831 {A : Type'} (P : A -> Prop) (x : A) : (term101 A P x) = (P x).
Proof. exact (@lem8830 (P x)). Qed.
Lemma lem8832 {A : Type'} (P : A -> Prop) (x : A) : (term100 A P x) = (P x).
Proof. exact (TRANS (@lem8828 A P x) (@lem8831 A P x)). Qed.
Lemma lem8833 {A : Type'} (P : A -> Prop) (x : A) : (term84 A P x) = (P x).
Proof. exact (TRANS (@lem8818 A P x) (@lem8832 A P x)). Qed.
Lemma lem8834 {A : Type'} (P : A -> Prop) (x : A) : (term65 A P x) = (term65 A P x).
Proof. exact (eq_refl (term65 A P x)). Qed.
Lemma lem8835 {A : Type'} (P : A -> Prop) (x : A) : (term85 A P x) = (term102 A P x).
Proof. exact (MK_COMB (@lem8834 A P x) (@lem8833 A P x)). Qed.
Lemma lem8838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8839 {A : Type'} (P : A -> Prop) (x : A) : (term86 A P x) = (term103 A P x).
Proof. exact (MK_COMB (@lem8838) (@lem8835 A P x)). Qed.
Lemma lem8854 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8855 {A : Type'} (P : A -> Prop) (x : A) : ((term85 A P x) = (term38 A P x)) = ((term102 A P x) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8839 A P x) (@lem8854 A P x)). Qed.
Lemma lem8858 {A : Type'} (P : A -> Prop) (x : A) : ((term102 A P x) = (term38 A P x)) = ((term85 A P x) = (term38 A P x)).
Proof. exact (SYM (@lem8855 A P x)). Qed.
Lemma lem8866 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem8867 {A : Type'} (P : A -> Prop) (x : A) : (term102 A P x) = (term38 A P x).
Proof. exact (@lem8866 (P x) (term63 A P x)). Qed.
Lemma lem8883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8884 {A : Type'} (P : A -> Prop) (x : A) : (term103 A P x) = (term104 A P x).
Proof. exact (MK_COMB (@lem8883) (@lem8867 A P x)). Qed.
Lemma lem8900 {A : Type'} (P : A -> Prop) (x : A) : (term38 A P x) = (term38 A P x).
Proof. exact (eq_refl (term38 A P x)). Qed.
Lemma lem8901 {A : Type'} (P : A -> Prop) (x : A) : ((term102 A P x) = (term38 A P x)) = ((term38 A P x) = (term38 A P x)).
Proof. exact (MK_COMB (@lem8884 A P x) (@lem8900 A P x)). Qed.
Lemma lem8903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8904 (x : Prop) : (x = x) = True.
Proof. exact (@lem8903 Prop x). Qed.
Lemma lem8905 {A : Type'} (P : A -> Prop) (x : A) : ((term38 A P x) = (term38 A P x)) = True.
Proof. exact (@lem8904 (term38 A P x)). Qed.
Lemma lem8906 {A : Type'} (P : A -> Prop) (x : A) : ((term102 A P x) = (term38 A P x)) = True.
Proof. exact (TRANS (@lem8901 A P x) (@lem8905 A P x)). Qed.
Lemma lem8907 {A : Type'} (P : A -> Prop) (x : A) : True = ((term102 A P x) = (term38 A P x)).
Proof. exact (SYM (@lem8906 A P x)). Qed.
Lemma lem8908 {A : Type'} (P : A -> Prop) (x : A) : (term102 A P x) = (term38 A P x).
Proof. exact (EQ_MP (@lem8907 A P x) (@lem0)). Qed.
Lemma lem8909 {A : Type'} (P : A -> Prop) (x : A) : (term85 A P x) = (term38 A P x).
Proof. exact (EQ_MP (@lem8858 A P x) (@lem8908 A P x)). Qed.
Lemma lem8910 {A : Type'} (P : A -> Prop) (x : A) : (term69 A x P) = (term38 A P x).
Proof. exact (EQ_MP (@lem8778 A P x) (@lem8909 A P x)). Qed.
Lemma lem8911 {A : Type'} (P : A -> Prop) (x : A) : (term49 A x P) = (term38 A P x).
Proof. exact (EQ_MP (@lem8356 A P x) (@lem8910 A P x)). Qed.
Lemma lem8912 {A : Type'} (P : A -> Prop) (x : A) : (term35 A x P) = (term38 A P x).
Proof. exact (EQ_MP (@lem8290 A P x) (@lem8911 A P x)). Qed.
Lemma lem8913 {A : Type'} (P : A -> Prop) (x : A) : (term34 A P x) = (term38 A P x).
Proof. exact (EQ_MP (@lem8267 A P x) (@lem8912 A P x)). Qed.
Lemma lem8916 {A : Type'} (P : A -> Prop) : (term105 A P) = (term106 A P).
Proof. exact (fun_ext (fun x : A => @lem8913 A P x)). Qed.
Lemma lem8917 {A : Type'} (P : A -> Prop) : (term27 A P) = (term30 A P).
Proof. exact (MK_COMB (@lem8256 A) (@lem8916 A P)). Qed.
Lemma lem8918 {A : Type'} (P : A -> Prop) : (term26 A P) = (term30 A P).
Proof. exact (EQ_MP (@lem8255 A P) (@lem8917 A P)). Qed.
Lemma lem8923 {A : Type'} : term107 A.
Proof. exact (fun P : A -> Prop => @lem8918 A P). Qed.
