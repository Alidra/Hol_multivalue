Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_IMAGE_INJ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INFINITE_IMAGE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Lemma lem3626962 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3626963 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3626964 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3626963 t1) (@lem3626962 t1)). Qed.
Lemma lem3626965 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3626964 t1 t2). Qed.
Lemma lem3626966 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3626967 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3626966 t1 t2) (@lem3626965 t1 t2)). Qed.
Lemma lem3626968 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3626967 t1 t2 t3). Qed.
Lemma lem3626969 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3626970 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3626969 t1 t2 t3) (@lem3626968 t1 t2 t3)). Qed.
Lemma lem3626971 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3626970 t1 t2 t3)). Qed.
Lemma lem3626973 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3626974 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem3626973 (term8 A B)). Qed.
Lemma lem3626975 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem3626974 A B)). Qed.
Lemma lem3626976 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3626977 {A B : Type'} : term11 A B.
Proof. exact (@lem3626961 A B). Qed.
Lemma lem3626978 {B : Type'} : term12 B.
Proof. exact (@lem3626961 B B). Qed.
Lemma lem3626980 {A : Type'} : term12 A.
Proof. exact (@lem3626961 A A). Qed.
Lemma lem3626988 {A B : Type'} (h1 : term13 A B) : term13 A B.
Proof. exact (h1). Qed.
Lemma lem3626989 {A B : Type'} : term14 A B.
Proof. exact (fun h0 : term13 A B => @lem3626988 A B h0). Qed.
Lemma lem3626990 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (h1). Qed.
Lemma lem3626991 {A B : Type'} (h1 : term13 A B) : term13 A B.
Proof. exact (h1). Qed.
Lemma lem3626992 {A B : Type'} (h1 : term13 A B) (h2 : term14 A B) : term13 A B.
Proof. exact (@lem3626990 A B h2 (@lem3626991 A B h1)). Qed.
Lemma lem3626993 {A B : Type'} (h1 : term13 A B) : term15 A B.
Proof. exact (fun h0 : term14 A B => @lem3626992 A B h1 h0). Qed.
Lemma lem3626994 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (h1). Qed.
Lemma lem3626995 {A B : Type'} (h1 : term13 A B) (h2 : term14 A B) : term13 A B.
Proof. exact (@lem3626993 A B h1 (@lem3626994 A B h2)). Qed.
Lemma lem3626996 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (fun h0 : term13 A B => @lem3626995 A B h0 h1). Qed.
Lemma lem3626997 {A B : Type'} : term16 A B.
Proof. exact (fun h0 : term14 A B => @lem3626996 A B h0). Qed.
Lemma lem3627000 {A B : Type'} : term14 A B.
Proof. exact (@lem3626997 A B (@lem3626989 A B)). Qed.
Lemma lem3627001 {A B : Type'} : term14 A B.
Proof. exact (@lem3627000 A B). Qed.
Lemma lem3627083 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3627084 {B : Type'} : (term17 B) = (term18 B).
Proof. exact (@lem3627083 (term12 B)). Qed.
Lemma lem3627111 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (eq_refl (term19 A B)). Qed.
Lemma lem3627112 {A B : Type'} : (term20 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem3627111 A B) (@lem3627084 B)). Qed.
Lemma lem3627115 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (eq_refl (term22 A)). Qed.
Lemma lem3627116 {A B : Type'} : (term23 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3627115 A) (@lem3627112 A B)). Qed.
Lemma lem3627119 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (eq_refl (term25 A B)). Qed.
Lemma lem3627126 {A B : Type'} : (term13 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem3627119 A B) (@lem3627116 A B)). Qed.
Lemma lem3627127 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3627140 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term28 B s f x y) = (term28 B s f x y).
Proof. exact (eq_refl (term28 B s f x y)). Qed.
Lemma lem3627141 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term29 B s f x) = (term29 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3627140 B s f x y)). Qed.
Lemma lem3627142 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3627143 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term30 B s f x) = (term30 B s f x).
Proof. exact (MK_COMB (@lem3627142 B) (@lem3627141 B s f x)). Qed.
Lemma lem3627144 {B : Type'} (s : B -> Prop) (f : B -> B) : (term31 B s f) = (term31 B s f).
Proof. exact (fun_ext (fun x : B => @lem3627143 B s f x)). Qed.
Lemma lem3627145 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3627146 {B : Type'} (s : B -> Prop) (f : B -> B) : (term32 B s f) = (term32 B s f).
Proof. exact (MK_COMB (@lem3627145 B) (@lem3627144 B s f)). Qed.
Lemma lem3627149 {B : Type'} (s : B -> Prop) : (term33 B s) = (term33 B s).
Proof. exact (eq_refl (term33 B s)). Qed.
Lemma lem3627150 {B : Type'} (s : B -> Prop) (f : B -> B) : (term34 B s f) = (term34 B s f).
Proof. exact (MK_COMB (@lem3627149 B s) (@lem3627146 B s f)). Qed.
Lemma lem3627151 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627152 {B : Type'} (s : B -> Prop) (f : B -> B) : (term35 B s f) = (term35 B s f).
Proof. exact (MK_COMB (@lem3627151) (@lem3627150 B s f)). Qed.
Lemma lem3627153 {B : Type'} (f : B -> B) (s : B -> Prop) : (term36 B f s) = (term36 B f s).
Proof. exact (MK_COMB (@lem3627152 B s f) (@lem3627127 B f s)). Qed.
Lemma lem3627154 {B : Type'} (f : B -> B) : (term37 B f) = (term37 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3627153 B f s)). Qed.
Lemma lem3627155 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3627156 {B : Type'} (f : B -> B) : (term38 B f) = (term38 B f).
Proof. exact (MK_COMB (@lem3627155 B) (@lem3627154 B f)). Qed.
Lemma lem3627157 {B : Type'} : (term39 B) = (term39 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3627156 B f)). Qed.
Lemma lem3627158 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3627159 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem3627158 B) (@lem3627157 B)). Qed.
Lemma lem3627160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627161 {B : Type'} : (term18 B) = (term18 B).
Proof. exact (MK_COMB (@lem3627160) (@lem3627159 B)). Qed.
Lemma lem3627162 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3627175 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term41 A B s f x y) = (term41 A B s f x y).
Proof. exact (eq_refl (term41 A B s f x y)). Qed.
Lemma lem3627176 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term42 A B s f x) = (term42 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3627175 A B s f x y)). Qed.
Lemma lem3627177 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627178 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term43 A B s f x) = (term43 A B s f x).
Proof. exact (MK_COMB (@lem3627177 A) (@lem3627176 A B s f x)). Qed.
Lemma lem3627179 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term44 A B s f) = (term44 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3627178 A B s f x)). Qed.
Lemma lem3627180 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627181 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term45 A B s f) = (term45 A B s f).
Proof. exact (MK_COMB (@lem3627180 A) (@lem3627179 A B s f)). Qed.
Lemma lem3627184 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem3627185 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term46 A B s f) = (term46 A B s f).
Proof. exact (MK_COMB (@lem3627184 A s) (@lem3627181 A B s f)). Qed.
Lemma lem3627186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627187 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term47 A B s f) = (term47 A B s f).
Proof. exact (MK_COMB (@lem3627186) (@lem3627185 A B s f)). Qed.
Lemma lem3627188 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term48 A B f s).
Proof. exact (MK_COMB (@lem3627187 A B s f) (@lem3627162 A B f s)). Qed.
Lemma lem3627189 {A B : Type'} (f : A -> B) : (term49 A B f) = (term49 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627188 A B f s)). Qed.
Lemma lem3627190 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627191 {A B : Type'} (f : A -> B) : (term50 A B f) = (term50 A B f).
Proof. exact (MK_COMB (@lem3627190 A) (@lem3627189 A B f)). Qed.
Lemma lem3627192 {A B : Type'} : (term51 A B) = (term51 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3627191 A B f)). Qed.
Lemma lem3627193 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3627194 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem3627193 A B) (@lem3627192 A B)). Qed.
Lemma lem3627195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627196 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem3627195) (@lem3627194 A B)). Qed.
Lemma lem3627197 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (MK_COMB (@lem3627196 A B) (@lem3627161 B)). Qed.
Lemma lem3627198 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627211 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term28 A s f x y) = (term28 A s f x y).
Proof. exact (eq_refl (term28 A s f x y)). Qed.
Lemma lem3627212 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term29 A s f x) = (term29 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3627211 A s f x y)). Qed.
Lemma lem3627213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627214 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term30 A s f x) = (term30 A s f x).
Proof. exact (MK_COMB (@lem3627213 A) (@lem3627212 A s f x)). Qed.
Lemma lem3627215 {A : Type'} (s : A -> Prop) (f : A -> A) : (term31 A s f) = (term31 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627214 A s f x)). Qed.
Lemma lem3627216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627217 {A : Type'} (s : A -> Prop) (f : A -> A) : (term32 A s f) = (term32 A s f).
Proof. exact (MK_COMB (@lem3627216 A) (@lem3627215 A s f)). Qed.
Lemma lem3627220 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (eq_refl (term33 A s)). Qed.
Lemma lem3627221 {A : Type'} (s : A -> Prop) (f : A -> A) : (term34 A s f) = (term34 A s f).
Proof. exact (MK_COMB (@lem3627220 A s) (@lem3627217 A s f)). Qed.
Lemma lem3627222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627223 {A : Type'} (s : A -> Prop) (f : A -> A) : (term35 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem3627222) (@lem3627221 A s f)). Qed.
Lemma lem3627224 {A : Type'} (f : A -> A) (s : A -> Prop) : (term36 A f s) = (term36 A f s).
Proof. exact (MK_COMB (@lem3627223 A s f) (@lem3627198 A f s)). Qed.
Lemma lem3627225 {A : Type'} (f : A -> A) : (term37 A f) = (term37 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627224 A f s)). Qed.
Lemma lem3627226 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627227 {A : Type'} (f : A -> A) : (term38 A f) = (term38 A f).
Proof. exact (MK_COMB (@lem3627226 A) (@lem3627225 A f)). Qed.
Lemma lem3627228 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3627227 A f)). Qed.
Lemma lem3627229 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627230 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3627229 A) (@lem3627228 A)). Qed.
Lemma lem3627231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627232 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (MK_COMB (@lem3627231) (@lem3627230 A)). Qed.
Lemma lem3627233 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem3627232 A) (@lem3627197 A B)). Qed.
Lemma lem3627238 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term52 A B f s) = (term52 A B f s).
Proof. exact (eq_refl (term52 A B f s)). Qed.
Lemma lem3627239 {A B : Type'} (f : A -> B) : (term53 A B f) = (term53 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627238 A B f s)). Qed.
Lemma lem3627240 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627241 {A B : Type'} (f : A -> B) : (term54 A B f) = (term54 A B f).
Proof. exact (MK_COMB (@lem3627240 A) (@lem3627239 A B f)). Qed.
Lemma lem3627246 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term55 A B f x y) = (term55 A B f x y).
Proof. exact (eq_refl (term55 A B f x y)). Qed.
Lemma lem3627247 {A B : Type'} (f : A -> B) (x : A) : (term56 A B f x) = (term56 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3627246 A B f x y)). Qed.
Lemma lem3627248 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627249 {A B : Type'} (f : A -> B) (x : A) : (term57 A B f x) = (term57 A B f x).
Proof. exact (MK_COMB (@lem3627248 A) (@lem3627247 A B f x)). Qed.
Lemma lem3627250 {A B : Type'} (f : A -> B) : (term58 A B f) = (term58 A B f).
Proof. exact (fun_ext (fun x : A => @lem3627249 A B f x)). Qed.
Lemma lem3627251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627252 {A B : Type'} (f : A -> B) : (term59 A B f) = (term59 A B f).
Proof. exact (MK_COMB (@lem3627251 A) (@lem3627250 A B f)). Qed.
Lemma lem3627253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627254 {A B : Type'} (f : A -> B) : (term60 A B f) = (term60 A B f).
Proof. exact (MK_COMB (@lem3627253) (@lem3627252 A B f)). Qed.
Lemma lem3627255 {A B : Type'} (f : A -> B) : (term61 A B f) = (term61 A B f).
Proof. exact (MK_COMB (@lem3627254 A B f) (@lem3627241 A B f)). Qed.
Lemma lem3627256 {A B : Type'} : (term62 A B) = (term62 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3627255 A B f)). Qed.
Lemma lem3627257 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3627258 {A B : Type'} : (term8 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem3627257 A B) (@lem3627256 A B)). Qed.
Lemma lem3627259 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627260 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem3627259) (@lem3627258 A B)). Qed.
Lemma lem3627261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3627262 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3627261) (@lem3627260 A B)). Qed.
Lemma lem3627263 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem3627262 A B) (@lem3627233 A B)). Qed.
Lemma lem3627404 {A B : Type'} : (term13 A B) = (term26 A B).
Proof. exact (TRANS (@lem3627126 A B) (@lem3627263 A B)). Qed.
Lemma lem3627405 {A B : Type'} : (term26 A B) = (term13 A B).
Proof. exact (SYM (@lem3627404 A B)). Qed.
Lemma lem3627406 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3627407 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem3627408 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem3627409 {B : Type'} (h1 : term12 B) : term12 B.
Proof. exact (h1). Qed.
Lemma lem3627416 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term55 A B f x y) = (term63 A B f x y).
Proof. exact (@lem17265 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3627417 {A B : Type'} (f : A -> B) (x : A) : (term56 A B f x) = (term64 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3627416 A B f x y)). Qed.
Lemma lem3627418 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627419 {A B : Type'} (f : A -> B) (x : A) : (term57 A B f x) = (term65 A B f x).
Proof. exact (MK_COMB (@lem3627418 A) (@lem3627417 A B f x)). Qed.
Lemma lem3627420 {A B : Type'} (f : A -> B) : (term58 A B f) = (term66 A B f).
Proof. exact (fun_ext (fun x : A => @lem3627419 A B f x)). Qed.
Lemma lem3627421 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3627422 {A B : Type'} (f : A -> B) : (term59 A B f) = (term67 A B f).
Proof. exact (MK_COMB (@lem3627421 A) (@lem3627420 A B f)). Qed.
Lemma lem3627429 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term68 A B f s) = (term69 A B f s).
Proof. exact (@lem17362 (@INFINITE A s) (term40 A B f s)). Qed.
Lemma lem3627430 {A : Type'} (P : type686 A) : (term70 A P) = (term71 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3627431 {A B : Type'} (f : A -> B) : (term72 A B f) = (term73 A B f).
Proof. exact (@lem3627430 A (term53 A B f)). Qed.
Lemma lem3627432 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term74 A B f s) = (term52 A B f s).
Proof. exact (eq_refl (term74 A B f s)). Qed.
Lemma lem3627433 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627434 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term75 A B f s) = (term68 A B f s).
Proof. exact (MK_COMB (@lem3627433) (@lem3627432 A B f s)). Qed.
Lemma lem3627435 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term75 A B f s) = (term69 A B f s).
Proof. exact (TRANS (@lem3627434 A B f s) (@lem3627429 A B f s)). Qed.
Lemma lem3627436 {A B : Type'} (f : A -> B) : (term76 A B f) = (term77 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627435 A B f s)). Qed.
Lemma lem3627437 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3627438 {A B : Type'} (f : A -> B) : (term73 A B f) = (term78 A B f).
Proof. exact (MK_COMB (@lem3627437 A) (@lem3627436 A B f)). Qed.
Lemma lem3627439 {A B : Type'} (f : A -> B) : (term72 A B f) = (term78 A B f).
Proof. exact (TRANS (@lem3627431 A B f) (@lem3627438 A B f)). Qed.
Lemma lem3627440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3627441 {A B : Type'} (f : A -> B) : (term79 A B f) = (term80 A B f).
Proof. exact (MK_COMB (@lem3627440) (@lem3627422 A B f)). Qed.
Lemma lem3627442 {A B : Type'} (f : A -> B) : (term81 A B f) = (term82 A B f).
Proof. exact (MK_COMB (@lem3627441 A B f) (@lem3627439 A B f)). Qed.
Lemma lem3627443 {A B : Type'} (f : A -> B) : (term83 A B f) = (term81 A B f).
Proof. exact (@lem17362 (term59 A B f) (term54 A B f)). Qed.
Lemma lem3627444 {A B : Type'} (f : A -> B) : (term83 A B f) = (term82 A B f).
Proof. exact (TRANS (@lem3627443 A B f) (@lem3627442 A B f)). Qed.
Lemma lem3627445 {A B : Type'} (P : type572 A B) : (term84 A B P) = (term85 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem3627446 {A B : Type'} : (term10 A B) = (term86 A B).
Proof. exact (@lem3627445 A B (term62 A B)). Qed.
Lemma lem3627447 {A B : Type'} (f : A -> B) : (term87 A B f) = (term61 A B f).
Proof. exact (eq_refl (term87 A B f)). Qed.
Lemma lem3627448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627449 {A B : Type'} (f : A -> B) : (term88 A B f) = (term83 A B f).
Proof. exact (MK_COMB (@lem3627448) (@lem3627447 A B f)). Qed.
Lemma lem3627450 {A B : Type'} (f : A -> B) : (term88 A B f) = (term82 A B f).
Proof. exact (TRANS (@lem3627449 A B f) (@lem3627444 A B f)). Qed.
Lemma lem3627451 {A B : Type'} : (term89 A B) = (term90 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3627450 A B f)). Qed.
Lemma lem3627452 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3627453 {A B : Type'} : (term86 A B) = (term91 A B).
Proof. exact (MK_COMB (@lem3627452 A B) (@lem3627451 A B)). Qed.
Lemma lem3627454 {A B : Type'} : (term10 A B) = (term91 A B).
Proof. exact (TRANS (@lem3627446 A B) (@lem3627453 A B)). Qed.
Lemma lem3627585 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3627586 {A : Type'} (P : Prop) (Q : type686 A) : (term94 A P Q) = (term95 A P Q).
Proof. exact (@lem3627585 (A -> Prop) P Q). Qed.
Lemma lem3627587 {A B : Type'} (f : A -> B) : (term96 A B f) = (term97 A B f).
Proof. exact (@lem3627586 A (term67 A B f) (term77 A B f)). Qed.
Lemma lem3627588 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term98 A B f s) = (term69 A B f s).
Proof. exact (eq_refl (term98 A B f s)). Qed.
Lemma lem3627589 {A B : Type'} (f : A -> B) : (term99 A B f) = (term77 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627588 A B f s)). Qed.
Lemma lem3627590 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3627591 {A B : Type'} (f : A -> B) : (term100 A B f) = (term78 A B f).
Proof. exact (MK_COMB (@lem3627590 A) (@lem3627589 A B f)). Qed.
Lemma lem3627592 {A B : Type'} (f : A -> B) : (term80 A B f) = (term80 A B f).
Proof. exact (eq_refl (term80 A B f)). Qed.
Lemma lem3627593 {A B : Type'} (f : A -> B) : (term96 A B f) = (term82 A B f).
Proof. exact (MK_COMB (@lem3627592 A B f) (@lem3627591 A B f)). Qed.
Lemma lem3627594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627595 {A B : Type'} (f : A -> B) : (term101 A B f) = (term102 A B f).
Proof. exact (MK_COMB (@lem3627594) (@lem3627593 A B f)). Qed.
Lemma lem3627596 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term98 A B f s) = (term69 A B f s).
Proof. exact (eq_refl (term98 A B f s)). Qed.
Lemma lem3627597 {A B : Type'} (f : A -> B) : (term80 A B f) = (term80 A B f).
Proof. exact (eq_refl (term80 A B f)). Qed.
Lemma lem3627598 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term103 A B f s) = (term104 A B f s).
Proof. exact (MK_COMB (@lem3627597 A B f) (@lem3627596 A B f s)). Qed.
Lemma lem3627599 {A B : Type'} (f : A -> B) : (term105 A B f) = (term106 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627598 A B f s)). Qed.
Lemma lem3627600 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3627601 {A B : Type'} (f : A -> B) : (term97 A B f) = (term107 A B f).
Proof. exact (MK_COMB (@lem3627600 A) (@lem3627599 A B f)). Qed.
Lemma lem3627602 {A B : Type'} (f : A -> B) : ((term96 A B f) = (term97 A B f)) = ((term82 A B f) = (term107 A B f)).
Proof. exact (MK_COMB (@lem3627595 A B f) (@lem3627601 A B f)). Qed.
Lemma lem3627603 {A B : Type'} (f : A -> B) : (term82 A B f) = (term107 A B f).
Proof. exact (EQ_MP (@lem3627602 A B f) (@lem3627587 A B f)). Qed.
Lemma lem3627604 {A B : Type'} : (term90 A B) = (term108 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3627603 A B f)). Qed.
Lemma lem3627605 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3627607 {A B : Type'} : (term91 A B) = (term109 A B).
Proof. exact (MK_COMB (@lem3627605 A B) (@lem3627604 A B)). Qed.
Lemma lem3627608 {A B : Type'} : (term10 A B) = (term109 A B).
Proof. exact (TRANS (@lem3627454 A B) (@lem3627607 A B)). Qed.
Lemma lem3627609 {A B : Type'} (h1 : term10 A B) : term109 A B.
Proof. exact (EQ_MP (@lem3627608 A B) (@lem3627406 A B h1)). Qed.
Lemma lem3627625 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term110 A s f x y) = (term111 A s f x y).
Proof. exact (@lem17362 (term112 A s x f y) (x = y)). Qed.
Lemma lem3627626 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3627627 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term115 A s f x) = (term116 A s f x).
Proof. exact (@lem3627626 A (term29 A s f x)). Qed.
Lemma lem3627628 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term117 A s f x y) = (term28 A s f x y).
Proof. exact (eq_refl (term117 A s f x y)). Qed.
Lemma lem3627629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627630 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term118 A s f x y) = (term110 A s f x y).
Proof. exact (MK_COMB (@lem3627629) (@lem3627628 A s f x y)). Qed.
Lemma lem3627631 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term118 A s f x y) = (term111 A s f x y).
Proof. exact (TRANS (@lem3627630 A s f x y) (@lem3627625 A s f x y)). Qed.
Lemma lem3627632 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term119 A s f x) = (term120 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3627631 A s f x y)). Qed.
Lemma lem3627633 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627634 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term116 A s f x) = (term121 A s f x).
Proof. exact (MK_COMB (@lem3627633 A) (@lem3627632 A s f x)). Qed.
Lemma lem3627635 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term115 A s f x) = (term121 A s f x).
Proof. exact (TRANS (@lem3627627 A s f x) (@lem3627634 A s f x)). Qed.
Lemma lem3627636 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3627637 {A : Type'} (s : A -> Prop) (f : A -> A) : (term122 A s f) = (term123 A s f).
Proof. exact (@lem3627636 A (term31 A s f)). Qed.
Lemma lem3627638 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term124 A s f x) = (term30 A s f x).
Proof. exact (eq_refl (term124 A s f x)). Qed.
Lemma lem3627639 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3627640 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term125 A s f x) = (term115 A s f x).
Proof. exact (MK_COMB (@lem3627639) (@lem3627638 A s f x)). Qed.
Lemma lem3627641 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term125 A s f x) = (term121 A s f x).
Proof. exact (TRANS (@lem3627640 A s f x) (@lem3627635 A s f x)). Qed.
Lemma lem3627642 {A : Type'} (s : A -> Prop) (f : A -> A) : (term126 A s f) = (term127 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627641 A s f x)). Qed.
Lemma lem3627643 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627644 {A : Type'} (s : A -> Prop) (f : A -> A) : (term123 A s f) = (term128 A s f).
Proof. exact (MK_COMB (@lem3627643 A) (@lem3627642 A s f)). Qed.
Lemma lem3627645 {A : Type'} (s : A -> Prop) (f : A -> A) : (term122 A s f) = (term128 A s f).
Proof. exact (TRANS (@lem3627637 A s f) (@lem3627644 A s f)). Qed.
Lemma lem3627647 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3627648 {A : Type'} (s : A -> Prop) (f : A -> A) : (term130 A s f) = (term131 A s f).
Proof. exact (MK_COMB (@lem3627647 A s) (@lem3627645 A s f)). Qed.
Lemma lem3627649 {A : Type'} (s : A -> Prop) (f : A -> A) : (term132 A s f) = (term130 A s f).
Proof. exact (@lem17045 (@INFINITE A s) (term32 A s f)). Qed.
Lemma lem3627650 {A : Type'} (s : A -> Prop) (f : A -> A) : (term132 A s f) = (term131 A s f).
Proof. exact (TRANS (@lem3627649 A s f) (@lem3627648 A s f)). Qed.
Lemma lem3627651 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627653 {A : Type'} (s : A -> Prop) (f : A -> A) : (term133 A s f) = (term134 A s f).
Proof. exact (MK_COMB (@lem3627652) (@lem3627650 A s f)). Qed.
Lemma lem3627654 {A : Type'} (f : A -> A) (s : A -> Prop) : (term135 A f s) = (term136 A f s).
Proof. exact (MK_COMB (@lem3627653 A s f) (@lem3627651 A f s)). Qed.
Lemma lem3627655 {A : Type'} (f : A -> A) (s : A -> Prop) : (term36 A f s) = (term135 A f s).
Proof. exact (@lem17265 (term34 A s f) (term27 A f s)). Qed.
Lemma lem3627656 {A : Type'} (f : A -> A) (s : A -> Prop) : (term36 A f s) = (term136 A f s).
Proof. exact (TRANS (@lem3627655 A f s) (@lem3627654 A f s)). Qed.
Lemma lem3627657 {A : Type'} (f : A -> A) : (term37 A f) = (term137 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627656 A f s)). Qed.
Lemma lem3627658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627659 {A : Type'} (f : A -> A) : (term38 A f) = (term138 A f).
Proof. exact (MK_COMB (@lem3627658 A) (@lem3627657 A f)). Qed.
Lemma lem3627660 {A : Type'} : (term39 A) = (term139 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3627659 A f)). Qed.
Lemma lem3627661 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627662 {A : Type'} : (term12 A) = (term140 A).
Proof. exact (MK_COMB (@lem3627661 A) (@lem3627660 A)). Qed.
Lemma lem3627769 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3627770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (@lem3627769 A P Q). Qed.
Lemma lem3627771 {A : Type'} (s : A -> Prop) (f : A -> A) : (term143 A s f) = (term144 A s f).
Proof. exact (@lem3627770 A (term145 A s) (term127 A s f)). Qed.
Lemma lem3627772 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term146 A s f x) = (term121 A s f x).
Proof. exact (eq_refl (term146 A s f x)). Qed.
Lemma lem3627773 {A : Type'} (s : A -> Prop) (f : A -> A) : (term147 A s f) = (term127 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627772 A s f x)). Qed.
Lemma lem3627774 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627775 {A : Type'} (s : A -> Prop) (f : A -> A) : (term148 A s f) = (term128 A s f).
Proof. exact (MK_COMB (@lem3627774 A) (@lem3627773 A s f)). Qed.
Lemma lem3627776 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3627777 {A : Type'} (s : A -> Prop) (f : A -> A) : (term143 A s f) = (term131 A s f).
Proof. exact (MK_COMB (@lem3627776 A s) (@lem3627775 A s f)). Qed.
Lemma lem3627778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627779 {A : Type'} (s : A -> Prop) (f : A -> A) : (term149 A s f) = (term150 A s f).
Proof. exact (MK_COMB (@lem3627778) (@lem3627777 A s f)). Qed.
Lemma lem3627780 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term146 A s f x) = (term121 A s f x).
Proof. exact (eq_refl (term146 A s f x)). Qed.
Lemma lem3627781 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3627782 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term151 A s f x) = (term152 A s f x).
Proof. exact (MK_COMB (@lem3627781 A s) (@lem3627780 A s f x)). Qed.
Lemma lem3627783 {A : Type'} (s : A -> Prop) (f : A -> A) : (term153 A s f) = (term154 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627782 A s f x)). Qed.
Lemma lem3627784 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627785 {A : Type'} (s : A -> Prop) (f : A -> A) : (term144 A s f) = (term155 A s f).
Proof. exact (MK_COMB (@lem3627784 A) (@lem3627783 A s f)). Qed.
Lemma lem3627786 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term143 A s f) = (term144 A s f)) = ((term131 A s f) = (term155 A s f)).
Proof. exact (MK_COMB (@lem3627779 A s f) (@lem3627785 A s f)). Qed.
Lemma lem3627787 {A : Type'} (s : A -> Prop) (f : A -> A) : (term131 A s f) = (term155 A s f).
Proof. exact (EQ_MP (@lem3627786 A s f) (@lem3627771 A s f)). Qed.
Lemma lem3627789 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3627790 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (@lem3627789 A P Q). Qed.
Lemma lem3627791 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term156 A s f x) = (term157 A s f x).
Proof. exact (@lem3627790 A (term145 A s) (term120 A s f x)). Qed.
Lemma lem3627792 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term158 A s f x y) = (term111 A s f x y).
Proof. exact (eq_refl (term158 A s f x y)). Qed.
Lemma lem3627793 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term159 A s f x) = (term120 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3627792 A s f x y)). Qed.
Lemma lem3627794 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627795 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term160 A s f x) = (term121 A s f x).
Proof. exact (MK_COMB (@lem3627794 A) (@lem3627793 A s f x)). Qed.
Lemma lem3627796 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3627797 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term156 A s f x) = (term152 A s f x).
Proof. exact (MK_COMB (@lem3627796 A s) (@lem3627795 A s f x)). Qed.
Lemma lem3627798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627799 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term161 A s f x) = (term162 A s f x).
Proof. exact (MK_COMB (@lem3627798) (@lem3627797 A s f x)). Qed.
Lemma lem3627800 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term158 A s f x y) = (term111 A s f x y).
Proof. exact (eq_refl (term158 A s f x y)). Qed.
Lemma lem3627801 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3627802 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term163 A s f x y) = (term164 A s f x y).
Proof. exact (MK_COMB (@lem3627801 A s) (@lem3627800 A s f x y)). Qed.
Lemma lem3627803 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term165 A s f x) = (term166 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3627802 A s f x y)). Qed.
Lemma lem3627804 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627805 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term157 A s f x) = (term167 A s f x).
Proof. exact (MK_COMB (@lem3627804 A) (@lem3627803 A s f x)). Qed.
Lemma lem3627806 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : ((term156 A s f x) = (term157 A s f x)) = ((term152 A s f x) = (term167 A s f x)).
Proof. exact (MK_COMB (@lem3627799 A s f x) (@lem3627805 A s f x)). Qed.
Lemma lem3627807 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term152 A s f x) = (term167 A s f x).
Proof. exact (EQ_MP (@lem3627806 A s f x) (@lem3627791 A s f x)). Qed.
Lemma lem3627808 {A : Type'} (s : A -> Prop) (f : A -> A) : (term154 A s f) = (term168 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627807 A s f x)). Qed.
Lemma lem3627809 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627810 {A : Type'} (s : A -> Prop) (f : A -> A) : (term155 A s f) = (term169 A s f).
Proof. exact (MK_COMB (@lem3627809 A) (@lem3627808 A s f)). Qed.
Lemma lem3627811 {A : Type'} (s : A -> Prop) (f : A -> A) : (term131 A s f) = (term169 A s f).
Proof. exact (TRANS (@lem3627787 A s f) (@lem3627810 A s f)). Qed.
Lemma lem3627812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627813 {A : Type'} (s : A -> Prop) (f : A -> A) : (term134 A s f) = (term170 A s f).
Proof. exact (MK_COMB (@lem3627812) (@lem3627811 A s f)). Qed.
Lemma lem3627814 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627815 {A : Type'} (f : A -> A) (s : A -> Prop) : (term136 A f s) = (term171 A f s).
Proof. exact (MK_COMB (@lem3627813 A s f) (@lem3627814 A f s)). Qed.
Lemma lem3627817 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3627818 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem3627817 A P Q). Qed.
Lemma lem3627819 {A : Type'} (f : A -> A) (s : A -> Prop) : (term174 A f s) = (term175 A f s).
Proof. exact (@lem3627818 A (term168 A s f) (term27 A f s)). Qed.
Lemma lem3627820 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term176 A s f x) = (term167 A s f x).
Proof. exact (eq_refl (term176 A s f x)). Qed.
Lemma lem3627821 {A : Type'} (s : A -> Prop) (f : A -> A) : (term177 A s f) = (term168 A s f).
Proof. exact (fun_ext (fun x : A => @lem3627820 A s f x)). Qed.
Lemma lem3627822 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627823 {A : Type'} (s : A -> Prop) (f : A -> A) : (term178 A s f) = (term169 A s f).
Proof. exact (MK_COMB (@lem3627822 A) (@lem3627821 A s f)). Qed.
Lemma lem3627824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627825 {A : Type'} (s : A -> Prop) (f : A -> A) : (term179 A s f) = (term170 A s f).
Proof. exact (MK_COMB (@lem3627824) (@lem3627823 A s f)). Qed.
Lemma lem3627826 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627827 {A : Type'} (f : A -> A) (s : A -> Prop) : (term174 A f s) = (term171 A f s).
Proof. exact (MK_COMB (@lem3627825 A s f) (@lem3627826 A f s)). Qed.
Lemma lem3627828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627829 {A : Type'} (f : A -> A) (s : A -> Prop) : (term180 A f s) = (term181 A f s).
Proof. exact (MK_COMB (@lem3627828) (@lem3627827 A f s)). Qed.
Lemma lem3627830 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term176 A s f x) = (term167 A s f x).
Proof. exact (eq_refl (term176 A s f x)). Qed.
Lemma lem3627831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627832 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term182 A s f x) = (term183 A s f x).
Proof. exact (MK_COMB (@lem3627831) (@lem3627830 A s f x)). Qed.
Lemma lem3627833 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627834 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term184 A x f s) = (term185 A x f s).
Proof. exact (MK_COMB (@lem3627832 A s f x) (@lem3627833 A f s)). Qed.
Lemma lem3627835 {A : Type'} (f : A -> A) (s : A -> Prop) : (term186 A f s) = (term187 A f s).
Proof. exact (fun_ext (fun x : A => @lem3627834 A x f s)). Qed.
Lemma lem3627836 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627837 {A : Type'} (f : A -> A) (s : A -> Prop) : (term175 A f s) = (term188 A f s).
Proof. exact (MK_COMB (@lem3627836 A) (@lem3627835 A f s)). Qed.
Lemma lem3627838 {A : Type'} (f : A -> A) (s : A -> Prop) : ((term174 A f s) = (term175 A f s)) = ((term171 A f s) = (term188 A f s)).
Proof. exact (MK_COMB (@lem3627829 A f s) (@lem3627837 A f s)). Qed.
Lemma lem3627839 {A : Type'} (f : A -> A) (s : A -> Prop) : (term171 A f s) = (term188 A f s).
Proof. exact (EQ_MP (@lem3627838 A f s) (@lem3627819 A f s)). Qed.
Lemma lem3627841 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3627842 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem3627841 A P Q). Qed.
Lemma lem3627843 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term189 A x f s) = (term190 A x f s).
Proof. exact (@lem3627842 A (term166 A s f x) (term27 A f s)). Qed.
Lemma lem3627844 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term191 A s f x y) = (term164 A s f x y).
Proof. exact (eq_refl (term191 A s f x y)). Qed.
Lemma lem3627845 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term192 A s f x) = (term166 A s f x).
Proof. exact (fun_ext (fun y : A => @lem3627844 A s f x y)). Qed.
Lemma lem3627846 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627847 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term193 A s f x) = (term167 A s f x).
Proof. exact (MK_COMB (@lem3627846 A) (@lem3627845 A s f x)). Qed.
Lemma lem3627848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627849 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) : (term194 A s f x) = (term183 A s f x).
Proof. exact (MK_COMB (@lem3627848) (@lem3627847 A s f x)). Qed.
Lemma lem3627850 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627851 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term189 A x f s) = (term185 A x f s).
Proof. exact (MK_COMB (@lem3627849 A s f x) (@lem3627850 A f s)). Qed.
Lemma lem3627852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627853 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term195 A x f s) = (term196 A x f s).
Proof. exact (MK_COMB (@lem3627852) (@lem3627851 A x f s)). Qed.
Lemma lem3627854 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term191 A s f x y) = (term164 A s f x y).
Proof. exact (eq_refl (term191 A s f x y)). Qed.
Lemma lem3627855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3627856 {A : Type'} (s : A -> Prop) (f : A -> A) (x : A) (y : A) : (term197 A s f x y) = (term198 A s f x y).
Proof. exact (MK_COMB (@lem3627855) (@lem3627854 A s f x y)). Qed.
Lemma lem3627857 {A : Type'} (f : A -> A) (s : A -> Prop) : (term27 A f s) = (term27 A f s).
Proof. exact (eq_refl (term27 A f s)). Qed.
Lemma lem3627858 {A : Type'} (x : A) (y : A) (f : A -> A) (s : A -> Prop) : (term199 A x y f s) = (term200 A x y f s).
Proof. exact (MK_COMB (@lem3627856 A s f x y) (@lem3627857 A f s)). Qed.
Lemma lem3627859 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term201 A x f s) = (term202 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3627858 A x y f s)). Qed.
Lemma lem3627860 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627861 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term190 A x f s) = (term203 A x f s).
Proof. exact (MK_COMB (@lem3627860 A) (@lem3627859 A x f s)). Qed.
Lemma lem3627862 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : ((term189 A x f s) = (term190 A x f s)) = ((term185 A x f s) = (term203 A x f s)).
Proof. exact (MK_COMB (@lem3627853 A x f s) (@lem3627861 A x f s)). Qed.
Lemma lem3627863 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term185 A x f s) = (term203 A x f s).
Proof. exact (EQ_MP (@lem3627862 A x f s) (@lem3627843 A x f s)). Qed.
Lemma lem3627864 {A : Type'} (f : A -> A) (s : A -> Prop) : (term187 A f s) = (term204 A f s).
Proof. exact (fun_ext (fun x : A => @lem3627863 A x f s)). Qed.
Lemma lem3627865 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627866 {A : Type'} (f : A -> A) (s : A -> Prop) : (term188 A f s) = (term205 A f s).
Proof. exact (MK_COMB (@lem3627865 A) (@lem3627864 A f s)). Qed.
Lemma lem3627867 {A : Type'} (f : A -> A) (s : A -> Prop) : (term171 A f s) = (term205 A f s).
Proof. exact (TRANS (@lem3627839 A f s) (@lem3627866 A f s)). Qed.
Lemma lem3627868 {A : Type'} (f : A -> A) (s : A -> Prop) : (term136 A f s) = (term205 A f s).
Proof. exact (TRANS (@lem3627815 A f s) (@lem3627867 A f s)). Qed.
Lemma lem3627869 {A : Type'} (f : A -> A) : (term137 A f) = (term206 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627868 A f s)). Qed.
Lemma lem3627870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627871 {A : Type'} (f : A -> A) : (term138 A f) = (term207 A f).
Proof. exact (MK_COMB (@lem3627870 A) (@lem3627869 A f)). Qed.
Lemma lem3627873 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3627874 {A : Type'} (P : type672 A) : (term210 A P) = (term211 A P).
Proof. exact (@lem3627873 (A -> Prop) A P). Qed.
Lemma lem3627875 {A : Type'} (f : A -> A) : (term212 A f) = (term213 A f).
Proof. exact (@lem3627874 A (term214 A f)). Qed.
Lemma lem3627876 {A : Type'} (f : A -> A) (s : A -> Prop) : (term215 A f s) = (term204 A f s).
Proof. exact (eq_refl (term215 A f s)). Qed.
Lemma lem3627877 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3627878 {A : Type'} (f : A -> A) (s : A -> Prop) (x : A) : (term216 A f s x) = (term217 A f s x).
Proof. exact (MK_COMB (@lem3627876 A f s) (@lem3627877 A x)). Qed.
Lemma lem3627879 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term217 A f s x) = (term203 A x f s).
Proof. exact (eq_refl (term217 A f s x)). Qed.
Lemma lem3627880 {A : Type'} (x : A) (f : A -> A) (s : A -> Prop) : (term216 A f s x) = (term203 A x f s).
Proof. exact (TRANS (@lem3627878 A f s x) (@lem3627879 A x f s)). Qed.
Lemma lem3627881 {A : Type'} (f : A -> A) (s : A -> Prop) : (term218 A f s) = (term204 A f s).
Proof. exact (fun_ext (fun x : A => @lem3627880 A x f s)). Qed.
Lemma lem3627882 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627883 {A : Type'} (f : A -> A) (s : A -> Prop) : (term219 A f s) = (term205 A f s).
Proof. exact (MK_COMB (@lem3627882 A) (@lem3627881 A f s)). Qed.
Lemma lem3627884 {A : Type'} (f : A -> A) : (term220 A f) = (term206 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627883 A f s)). Qed.
Lemma lem3627885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627886 {A : Type'} (f : A -> A) : (term212 A f) = (term207 A f).
Proof. exact (MK_COMB (@lem3627885 A) (@lem3627884 A f)). Qed.
Lemma lem3627887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627888 {A : Type'} (f : A -> A) : (term221 A f) = (term222 A f).
Proof. exact (MK_COMB (@lem3627887) (@lem3627886 A f)). Qed.
Lemma lem3627889 {A : Type'} (f : A -> A) (s : A -> Prop) : (term215 A f s) = (term204 A f s).
Proof. exact (eq_refl (term215 A f s)). Qed.
Lemma lem3627890 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3627891 {A : Type'} (f : A -> A) (x : type684 A) (s : A -> Prop) : (term223 A f x s) = (term224 A f x s).
Proof. exact (MK_COMB (@lem3627889 A f s) (@lem3627890 A x s)). Qed.
Lemma lem3627892 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term224 A f x s) = (term225 A x f s).
Proof. exact (eq_refl (term224 A f x s)). Qed.
Lemma lem3627893 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term223 A f x s) = (term225 A x f s).
Proof. exact (TRANS (@lem3627891 A f x s) (@lem3627892 A x f s)). Qed.
Lemma lem3627894 {A : Type'} (x : type684 A) (f : A -> A) : (term226 A f x) = (term227 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627893 A x f s)). Qed.
Lemma lem3627895 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627896 {A : Type'} (x : type684 A) (f : A -> A) : (term228 A f x) = (term229 A x f).
Proof. exact (MK_COMB (@lem3627895 A) (@lem3627894 A x f)). Qed.
Lemma lem3627897 {A : Type'} (f : A -> A) : (term230 A f) = (term231 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3627896 A x f)). Qed.
Lemma lem3627898 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3627899 {A : Type'} (f : A -> A) : (term213 A f) = (term232 A f).
Proof. exact (MK_COMB (@lem3627898 A) (@lem3627897 A f)). Qed.
Lemma lem3627900 {A : Type'} (f : A -> A) : ((term212 A f) = (term213 A f)) = ((term207 A f) = (term232 A f)).
Proof. exact (MK_COMB (@lem3627888 A f) (@lem3627899 A f)). Qed.
Lemma lem3627901 {A : Type'} (f : A -> A) : (term207 A f) = (term232 A f).
Proof. exact (EQ_MP (@lem3627900 A f) (@lem3627875 A f)). Qed.
Lemma lem3627903 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3627904 {A : Type'} (P : type672 A) : (term210 A P) = (term211 A P).
Proof. exact (@lem3627903 (A -> Prop) A P). Qed.
Lemma lem3627905 {A : Type'} (x : type684 A) (f : A -> A) : (term233 A x f) = (term234 A x f).
Proof. exact (@lem3627904 A (term235 A x f)). Qed.
Lemma lem3627906 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term236 A x f s) = (term237 A x f s).
Proof. exact (eq_refl (term236 A x f s)). Qed.
Lemma lem3627907 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3627908 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) (y : A) : (term238 A x f s y) = (term239 A x f s y).
Proof. exact (MK_COMB (@lem3627906 A x f s) (@lem3627907 A y)). Qed.
Lemma lem3627909 {A : Type'} (x : type684 A) (y : A) (f : A -> A) (s : A -> Prop) : (term239 A x f s y) = (term240 A x y f s).
Proof. exact (eq_refl (term239 A x f s y)). Qed.
Lemma lem3627910 {A : Type'} (x : type684 A) (y : A) (f : A -> A) (s : A -> Prop) : (term238 A x f s y) = (term240 A x y f s).
Proof. exact (TRANS (@lem3627908 A x f s y) (@lem3627909 A x y f s)). Qed.
Lemma lem3627911 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term241 A x f s) = (term237 A x f s).
Proof. exact (fun_ext (fun y : A => @lem3627910 A x y f s)). Qed.
Lemma lem3627912 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3627913 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term242 A x f s) = (term225 A x f s).
Proof. exact (MK_COMB (@lem3627912 A) (@lem3627911 A x f s)). Qed.
Lemma lem3627914 {A : Type'} (x : type684 A) (f : A -> A) : (term243 A x f) = (term227 A x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627913 A x f s)). Qed.
Lemma lem3627915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627916 {A : Type'} (x : type684 A) (f : A -> A) : (term233 A x f) = (term229 A x f).
Proof. exact (MK_COMB (@lem3627915 A) (@lem3627914 A x f)). Qed.
Lemma lem3627917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627918 {A : Type'} (x : type684 A) (f : A -> A) : (term244 A x f) = (term245 A x f).
Proof. exact (MK_COMB (@lem3627917) (@lem3627916 A x f)). Qed.
Lemma lem3627919 {A : Type'} (x : type684 A) (f : A -> A) (s : A -> Prop) : (term236 A x f s) = (term237 A x f s).
Proof. exact (eq_refl (term236 A x f s)). Qed.
Lemma lem3627920 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3627921 {A : Type'} (x : type684 A) (f : A -> A) (y : type684 A) (s : A -> Prop) : (term246 A x f y s) = (term247 A x f y s).
Proof. exact (MK_COMB (@lem3627919 A x f s) (@lem3627920 A y s)). Qed.
Lemma lem3627922 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) (s : A -> Prop) : (term247 A x f y s) = (term248 A x y f s).
Proof. exact (eq_refl (term247 A x f y s)). Qed.
Lemma lem3627923 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) (s : A -> Prop) : (term246 A x f y s) = (term248 A x y f s).
Proof. exact (TRANS (@lem3627921 A x f y s) (@lem3627922 A x y f s)). Qed.
Lemma lem3627924 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) : (term249 A x f y) = (term250 A x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3627923 A x y f s)). Qed.
Lemma lem3627925 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3627926 {A : Type'} (x : type684 A) (y : type684 A) (f : A -> A) : (term251 A x f y) = (term252 A x y f).
Proof. exact (MK_COMB (@lem3627925 A) (@lem3627924 A x y f)). Qed.
Lemma lem3627927 {A : Type'} (x : type684 A) (f : A -> A) : (term253 A x f) = (term254 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3627926 A x y f)). Qed.
Lemma lem3627928 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3627929 {A : Type'} (x : type684 A) (f : A -> A) : (term234 A x f) = (term255 A x f).
Proof. exact (MK_COMB (@lem3627928 A) (@lem3627927 A x f)). Qed.
Lemma lem3627930 {A : Type'} (x : type684 A) (f : A -> A) : ((term233 A x f) = (term234 A x f)) = ((term229 A x f) = (term255 A x f)).
Proof. exact (MK_COMB (@lem3627918 A x f) (@lem3627929 A x f)). Qed.
Lemma lem3627931 {A : Type'} (x : type684 A) (f : A -> A) : (term229 A x f) = (term255 A x f).
Proof. exact (EQ_MP (@lem3627930 A x f) (@lem3627905 A x f)). Qed.
Lemma lem3627932 {A : Type'} (f : A -> A) : (term231 A f) = (term256 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3627931 A x f)). Qed.
Lemma lem3627933 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3627934 {A : Type'} (f : A -> A) : (term232 A f) = (term257 A f).
Proof. exact (MK_COMB (@lem3627933 A) (@lem3627932 A f)). Qed.
Lemma lem3627935 {A : Type'} (f : A -> A) : (term207 A f) = (term257 A f).
Proof. exact (TRANS (@lem3627901 A f) (@lem3627934 A f)). Qed.
Lemma lem3627936 {A : Type'} (f : A -> A) : (term138 A f) = (term257 A f).
Proof. exact (TRANS (@lem3627871 A f) (@lem3627935 A f)). Qed.
Lemma lem3627937 {A : Type'} : (term139 A) = (term258 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3627936 A f)). Qed.
Lemma lem3627938 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627939 {A : Type'} : (term140 A) = (term259 A).
Proof. exact (MK_COMB (@lem3627938 A) (@lem3627937 A)). Qed.
Lemma lem3627941 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3627942 {A : Type'} (P : type481 A) : (term260 A P) = (term261 A P).
Proof. exact (@lem3627941 (A -> A) (type684 A) P). Qed.
Lemma lem3627943 {A : Type'} : (term262 A) = (term263 A).
Proof. exact (@lem3627942 A (term264 A)). Qed.
Lemma lem3627944 {A : Type'} (f : A -> A) : (term265 A f) = (term256 A f).
Proof. exact (eq_refl (term265 A f)). Qed.
Lemma lem3627945 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3627946 {A : Type'} (f : A -> A) (x : type684 A) : (term266 A f x) = (term267 A f x).
Proof. exact (MK_COMB (@lem3627944 A f) (@lem3627945 A x)). Qed.
Lemma lem3627947 {A : Type'} (x : type684 A) (f : A -> A) : (term267 A f x) = (term255 A x f).
Proof. exact (eq_refl (term267 A f x)). Qed.
Lemma lem3627948 {A : Type'} (x : type684 A) (f : A -> A) : (term266 A f x) = (term255 A x f).
Proof. exact (TRANS (@lem3627946 A f x) (@lem3627947 A x f)). Qed.
Lemma lem3627949 {A : Type'} (f : A -> A) : (term268 A f) = (term256 A f).
Proof. exact (fun_ext (fun x : type684 A => @lem3627948 A x f)). Qed.
Lemma lem3627950 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3627951 {A : Type'} (f : A -> A) : (term269 A f) = (term257 A f).
Proof. exact (MK_COMB (@lem3627950 A) (@lem3627949 A f)). Qed.
Lemma lem3627952 {A : Type'} : (term270 A) = (term258 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3627951 A f)). Qed.
Lemma lem3627953 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627954 {A : Type'} : (term262 A) = (term259 A).
Proof. exact (MK_COMB (@lem3627953 A) (@lem3627952 A)). Qed.
Lemma lem3627955 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627956 {A : Type'} : (term271 A) = (term272 A).
Proof. exact (MK_COMB (@lem3627955) (@lem3627954 A)). Qed.
Lemma lem3627957 {A : Type'} (f : A -> A) : (term265 A f) = (term256 A f).
Proof. exact (eq_refl (term265 A f)). Qed.
Lemma lem3627958 {A : Type'} (x : type485 A) (f : A -> A) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3627959 {A : Type'} (x : type485 A) (f : A -> A) : (term273 A x f) = (term274 A x f).
Proof. exact (MK_COMB (@lem3627957 A f) (@lem3627958 A x f)). Qed.
Lemma lem3627960 {A : Type'} (x : type485 A) (f : A -> A) : (term274 A x f) = (term275 A x f).
Proof. exact (eq_refl (term274 A x f)). Qed.
Lemma lem3627961 {A : Type'} (x : type485 A) (f : A -> A) : (term273 A x f) = (term275 A x f).
Proof. exact (TRANS (@lem3627959 A x f) (@lem3627960 A x f)). Qed.
Lemma lem3627962 {A : Type'} (x : type485 A) : (term276 A x) = (term277 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem3627961 A x f)). Qed.
Lemma lem3627963 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627964 {A : Type'} (x : type485 A) : (term278 A x) = (term279 A x).
Proof. exact (MK_COMB (@lem3627963 A) (@lem3627962 A x)). Qed.
Lemma lem3627965 {A : Type'} : (term280 A) = (term281 A).
Proof. exact (fun_ext (fun x : type485 A => @lem3627964 A x)). Qed.
Lemma lem3627966 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3627967 {A : Type'} : (term263 A) = (term282 A).
Proof. exact (MK_COMB (@lem3627966 A) (@lem3627965 A)). Qed.
Lemma lem3627968 {A : Type'} : ((term262 A) = (term263 A)) = ((term259 A) = (term282 A)).
Proof. exact (MK_COMB (@lem3627956 A) (@lem3627967 A)). Qed.
Lemma lem3627969 {A : Type'} : (term259 A) = (term282 A).
Proof. exact (EQ_MP (@lem3627968 A) (@lem3627943 A)). Qed.
Lemma lem3627971 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3627972 {A : Type'} (P : type481 A) : (term260 A P) = (term261 A P).
Proof. exact (@lem3627971 (A -> A) (type684 A) P). Qed.
Lemma lem3627973 {A : Type'} (x : type485 A) : (term283 A x) = (term284 A x).
Proof. exact (@lem3627972 A (term285 A x)). Qed.
Lemma lem3627974 {A : Type'} (x : type485 A) (f : A -> A) : (term286 A x f) = (term287 A x f).
Proof. exact (eq_refl (term286 A x f)). Qed.
Lemma lem3627975 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3627976 {A : Type'} (x : type485 A) (f : A -> A) (y : type684 A) : (term288 A x f y) = (term289 A x f y).
Proof. exact (MK_COMB (@lem3627974 A x f) (@lem3627975 A y)). Qed.
Lemma lem3627977 {A : Type'} (x : type485 A) (y : type684 A) (f : A -> A) : (term289 A x f y) = (term290 A x y f).
Proof. exact (eq_refl (term289 A x f y)). Qed.
Lemma lem3627978 {A : Type'} (x : type485 A) (y : type684 A) (f : A -> A) : (term288 A x f y) = (term290 A x y f).
Proof. exact (TRANS (@lem3627976 A x f y) (@lem3627977 A x y f)). Qed.
Lemma lem3627979 {A : Type'} (x : type485 A) (f : A -> A) : (term291 A x f) = (term287 A x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3627978 A x y f)). Qed.
Lemma lem3627980 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3627981 {A : Type'} (x : type485 A) (f : A -> A) : (term292 A x f) = (term275 A x f).
Proof. exact (MK_COMB (@lem3627980 A) (@lem3627979 A x f)). Qed.
Lemma lem3627982 {A : Type'} (x : type485 A) : (term293 A x) = (term277 A x).
Proof. exact (fun_ext (fun f : A -> A => @lem3627981 A x f)). Qed.
Lemma lem3627983 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627984 {A : Type'} (x : type485 A) : (term283 A x) = (term279 A x).
Proof. exact (MK_COMB (@lem3627983 A) (@lem3627982 A x)). Qed.
Lemma lem3627985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3627986 {A : Type'} (x : type485 A) : (term294 A x) = (term295 A x).
Proof. exact (MK_COMB (@lem3627985) (@lem3627984 A x)). Qed.
Lemma lem3627987 {A : Type'} (x : type485 A) (f : A -> A) : (term286 A x f) = (term287 A x f).
Proof. exact (eq_refl (term286 A x f)). Qed.
Lemma lem3627988 {A : Type'} (y : type485 A) (f : A -> A) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3627989 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term296 A x y f) = (term297 A x y f).
Proof. exact (MK_COMB (@lem3627987 A x f) (@lem3627988 A y f)). Qed.
Lemma lem3627990 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term297 A x y f) = (term298 A x y f).
Proof. exact (eq_refl (term297 A x y f)). Qed.
Lemma lem3627991 {A : Type'} (x : type485 A) (y : type485 A) (f : A -> A) : (term296 A x y f) = (term298 A x y f).
Proof. exact (TRANS (@lem3627989 A x y f) (@lem3627990 A x y f)). Qed.
Lemma lem3627992 {A : Type'} (x : type485 A) (y : type485 A) : (term299 A x y) = (term300 A x y).
Proof. exact (fun_ext (fun f : A -> A => @lem3627991 A x y f)). Qed.
Lemma lem3627993 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3627994 {A : Type'} (x : type485 A) (y : type485 A) : (term301 A x y) = (term302 A x y).
Proof. exact (MK_COMB (@lem3627993 A) (@lem3627992 A x y)). Qed.
Lemma lem3627995 {A : Type'} (x : type485 A) : (term303 A x) = (term304 A x).
Proof. exact (fun_ext (fun y : type485 A => @lem3627994 A x y)). Qed.
Lemma lem3627996 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3627997 {A : Type'} (x : type485 A) : (term284 A x) = (term305 A x).
Proof. exact (MK_COMB (@lem3627996 A) (@lem3627995 A x)). Qed.
Lemma lem3627998 {A : Type'} (x : type485 A) : ((term283 A x) = (term284 A x)) = ((term279 A x) = (term305 A x)).
Proof. exact (MK_COMB (@lem3627986 A x) (@lem3627997 A x)). Qed.
Lemma lem3627999 {A : Type'} (x : type485 A) : (term279 A x) = (term305 A x).
Proof. exact (EQ_MP (@lem3627998 A x) (@lem3627973 A x)). Qed.
Lemma lem3628000 {A : Type'} : (term281 A) = (term306 A).
Proof. exact (fun_ext (fun x : type485 A => @lem3627999 A x)). Qed.
Lemma lem3628001 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> A)) = (@ex ((A -> A) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> A))). Qed.
Lemma lem3628002 {A : Type'} : (term282 A) = (term307 A).
Proof. exact (MK_COMB (@lem3628001 A) (@lem3628000 A)). Qed.
Lemma lem3628003 {A : Type'} : (term259 A) = (term307 A).
Proof. exact (TRANS (@lem3627969 A) (@lem3628002 A)). Qed.
Lemma lem3628005 {A : Type'} : (term140 A) = (term307 A).
Proof. exact (TRANS (@lem3627939 A) (@lem3628003 A)). Qed.
Lemma lem3628006 {A : Type'} : (term12 A) = (term307 A).
Proof. exact (TRANS (@lem3627662 A) (@lem3628005 A)). Qed.
Lemma lem3628007 {A : Type'} (h1 : term12 A) : term307 A.
Proof. exact (EQ_MP (@lem3628006 A) (@lem3627407 A h1)). Qed.
Lemma lem3628023 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term308 A B s f x y) = (term309 A B s f x y).
Proof. exact (@lem17362 (term310 A B s x f y) (x = y)). Qed.
Lemma lem3628024 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3628025 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term311 A B s f x) = (term312 A B s f x).
Proof. exact (@lem3628024 A (term42 A B s f x)). Qed.
Lemma lem3628026 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term313 A B s f x y) = (term41 A B s f x y).
Proof. exact (eq_refl (term313 A B s f x y)). Qed.
Lemma lem3628027 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3628028 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term314 A B s f x y) = (term308 A B s f x y).
Proof. exact (MK_COMB (@lem3628027) (@lem3628026 A B s f x y)). Qed.
Lemma lem3628029 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term314 A B s f x y) = (term309 A B s f x y).
Proof. exact (TRANS (@lem3628028 A B s f x y) (@lem3628023 A B s f x y)). Qed.
Lemma lem3628030 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term315 A B s f x) = (term316 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3628029 A B s f x y)). Qed.
Lemma lem3628031 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628032 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term312 A B s f x) = (term317 A B s f x).
Proof. exact (MK_COMB (@lem3628031 A) (@lem3628030 A B s f x)). Qed.
Lemma lem3628033 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term311 A B s f x) = (term317 A B s f x).
Proof. exact (TRANS (@lem3628025 A B s f x) (@lem3628032 A B s f x)). Qed.
Lemma lem3628034 {A : Type'} (P : A -> Prop) : (term113 A P) = (term114 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3628035 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term318 A B s f) = (term319 A B s f).
Proof. exact (@lem3628034 A (term44 A B s f)). Qed.
Lemma lem3628036 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term320 A B s f x) = (term43 A B s f x).
Proof. exact (eq_refl (term320 A B s f x)). Qed.
Lemma lem3628037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3628038 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term321 A B s f x) = (term311 A B s f x).
Proof. exact (MK_COMB (@lem3628037) (@lem3628036 A B s f x)). Qed.
Lemma lem3628039 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term321 A B s f x) = (term317 A B s f x).
Proof. exact (TRANS (@lem3628038 A B s f x) (@lem3628033 A B s f x)). Qed.
Lemma lem3628040 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term322 A B s f) = (term323 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3628039 A B s f x)). Qed.
Lemma lem3628041 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628042 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term319 A B s f) = (term324 A B s f).
Proof. exact (MK_COMB (@lem3628041 A) (@lem3628040 A B s f)). Qed.
Lemma lem3628043 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term318 A B s f) = (term324 A B s f).
Proof. exact (TRANS (@lem3628035 A B s f) (@lem3628042 A B s f)). Qed.
Lemma lem3628045 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3628046 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term325 A B s f) = (term326 A B s f).
Proof. exact (MK_COMB (@lem3628045 A s) (@lem3628043 A B s f)). Qed.
Lemma lem3628047 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term327 A B s f) = (term325 A B s f).
Proof. exact (@lem17045 (@INFINITE A s) (term45 A B s f)). Qed.
Lemma lem3628048 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term327 A B s f) = (term326 A B s f).
Proof. exact (TRANS (@lem3628047 A B s f) (@lem3628046 A B s f)). Qed.
Lemma lem3628049 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628051 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term328 A B s f) = (term329 A B s f).
Proof. exact (MK_COMB (@lem3628050) (@lem3628048 A B s f)). Qed.
Lemma lem3628052 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term330 A B f s) = (term331 A B f s).
Proof. exact (MK_COMB (@lem3628051 A B s f) (@lem3628049 A B f s)). Qed.
Lemma lem3628053 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term330 A B f s).
Proof. exact (@lem17265 (term46 A B s f) (term40 A B f s)). Qed.
Lemma lem3628054 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term48 A B f s) = (term331 A B f s).
Proof. exact (TRANS (@lem3628053 A B f s) (@lem3628052 A B f s)). Qed.
Lemma lem3628055 {A B : Type'} (f : A -> B) : (term49 A B f) = (term332 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628054 A B f s)). Qed.
Lemma lem3628056 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628057 {A B : Type'} (f : A -> B) : (term50 A B f) = (term333 A B f).
Proof. exact (MK_COMB (@lem3628056 A) (@lem3628055 A B f)). Qed.
Lemma lem3628058 {A B : Type'} : (term51 A B) = (term334 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3628057 A B f)). Qed.
Lemma lem3628059 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628060 {A B : Type'} : (term11 A B) = (term335 A B).
Proof. exact (MK_COMB (@lem3628059 A B) (@lem3628058 A B)). Qed.
Lemma lem3628167 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3628168 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (@lem3628167 A P Q). Qed.
Lemma lem3628169 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term336 A B s f) = (term337 A B s f).
Proof. exact (@lem3628168 A (term145 A s) (term323 A B s f)). Qed.
Lemma lem3628170 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term338 A B s f x) = (term317 A B s f x).
Proof. exact (eq_refl (term338 A B s f x)). Qed.
Lemma lem3628171 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term339 A B s f) = (term323 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3628170 A B s f x)). Qed.
Lemma lem3628172 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628173 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term340 A B s f) = (term324 A B s f).
Proof. exact (MK_COMB (@lem3628172 A) (@lem3628171 A B s f)). Qed.
Lemma lem3628174 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3628175 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term336 A B s f) = (term326 A B s f).
Proof. exact (MK_COMB (@lem3628174 A s) (@lem3628173 A B s f)). Qed.
Lemma lem3628176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628177 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term341 A B s f) = (term342 A B s f).
Proof. exact (MK_COMB (@lem3628176) (@lem3628175 A B s f)). Qed.
Lemma lem3628178 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term338 A B s f x) = (term317 A B s f x).
Proof. exact (eq_refl (term338 A B s f x)). Qed.
Lemma lem3628179 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3628180 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term343 A B s f x) = (term344 A B s f x).
Proof. exact (MK_COMB (@lem3628179 A s) (@lem3628178 A B s f x)). Qed.
Lemma lem3628181 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term345 A B s f) = (term346 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3628180 A B s f x)). Qed.
Lemma lem3628182 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628183 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term337 A B s f) = (term347 A B s f).
Proof. exact (MK_COMB (@lem3628182 A) (@lem3628181 A B s f)). Qed.
Lemma lem3628184 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term336 A B s f) = (term337 A B s f)) = ((term326 A B s f) = (term347 A B s f)).
Proof. exact (MK_COMB (@lem3628177 A B s f) (@lem3628183 A B s f)). Qed.
Lemma lem3628185 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term326 A B s f) = (term347 A B s f).
Proof. exact (EQ_MP (@lem3628184 A B s f) (@lem3628169 A B s f)). Qed.
Lemma lem3628187 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3628188 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (@lem3628187 A P Q). Qed.
Lemma lem3628189 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term348 A B s f x) = (term349 A B s f x).
Proof. exact (@lem3628188 A (term145 A s) (term316 A B s f x)). Qed.
Lemma lem3628190 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term350 A B s f x y) = (term309 A B s f x y).
Proof. exact (eq_refl (term350 A B s f x y)). Qed.
Lemma lem3628191 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term351 A B s f x) = (term316 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3628190 A B s f x y)). Qed.
Lemma lem3628192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628193 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term352 A B s f x) = (term317 A B s f x).
Proof. exact (MK_COMB (@lem3628192 A) (@lem3628191 A B s f x)). Qed.
Lemma lem3628194 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3628195 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term348 A B s f x) = (term344 A B s f x).
Proof. exact (MK_COMB (@lem3628194 A s) (@lem3628193 A B s f x)). Qed.
Lemma lem3628196 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628197 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term353 A B s f x) = (term354 A B s f x).
Proof. exact (MK_COMB (@lem3628196) (@lem3628195 A B s f x)). Qed.
Lemma lem3628198 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term350 A B s f x y) = (term309 A B s f x y).
Proof. exact (eq_refl (term350 A B s f x y)). Qed.
Lemma lem3628199 {A : Type'} (s : A -> Prop) : (term129 A s) = (term129 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3628200 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term355 A B s f x y) = (term356 A B s f x y).
Proof. exact (MK_COMB (@lem3628199 A s) (@lem3628198 A B s f x y)). Qed.
Lemma lem3628201 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term357 A B s f x) = (term358 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3628200 A B s f x y)). Qed.
Lemma lem3628202 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628203 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term349 A B s f x) = (term359 A B s f x).
Proof. exact (MK_COMB (@lem3628202 A) (@lem3628201 A B s f x)). Qed.
Lemma lem3628204 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term348 A B s f x) = (term349 A B s f x)) = ((term344 A B s f x) = (term359 A B s f x)).
Proof. exact (MK_COMB (@lem3628197 A B s f x) (@lem3628203 A B s f x)). Qed.
Lemma lem3628205 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term344 A B s f x) = (term359 A B s f x).
Proof. exact (EQ_MP (@lem3628204 A B s f x) (@lem3628189 A B s f x)). Qed.
Lemma lem3628206 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term346 A B s f) = (term360 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3628205 A B s f x)). Qed.
Lemma lem3628207 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628208 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term347 A B s f) = (term361 A B s f).
Proof. exact (MK_COMB (@lem3628207 A) (@lem3628206 A B s f)). Qed.
Lemma lem3628209 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term326 A B s f) = (term361 A B s f).
Proof. exact (TRANS (@lem3628185 A B s f) (@lem3628208 A B s f)). Qed.
Lemma lem3628210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628211 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term329 A B s f) = (term362 A B s f).
Proof. exact (MK_COMB (@lem3628210) (@lem3628209 A B s f)). Qed.
Lemma lem3628212 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628213 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term331 A B f s) = (term363 A B f s).
Proof. exact (MK_COMB (@lem3628211 A B s f) (@lem3628212 A B f s)). Qed.
Lemma lem3628215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3628216 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem3628215 A P Q). Qed.
Lemma lem3628217 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term364 A B f s) = (term365 A B f s).
Proof. exact (@lem3628216 A (term360 A B s f) (term40 A B f s)). Qed.
Lemma lem3628218 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term366 A B s f x) = (term359 A B s f x).
Proof. exact (eq_refl (term366 A B s f x)). Qed.
Lemma lem3628219 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term367 A B s f) = (term360 A B s f).
Proof. exact (fun_ext (fun x : A => @lem3628218 A B s f x)). Qed.
Lemma lem3628220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628221 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term368 A B s f) = (term361 A B s f).
Proof. exact (MK_COMB (@lem3628220 A) (@lem3628219 A B s f)). Qed.
Lemma lem3628222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628223 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term369 A B s f) = (term362 A B s f).
Proof. exact (MK_COMB (@lem3628222) (@lem3628221 A B s f)). Qed.
Lemma lem3628224 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628225 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term364 A B f s) = (term363 A B f s).
Proof. exact (MK_COMB (@lem3628223 A B s f) (@lem3628224 A B f s)). Qed.
Lemma lem3628226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628227 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term370 A B f s) = (term371 A B f s).
Proof. exact (MK_COMB (@lem3628226) (@lem3628225 A B f s)). Qed.
Lemma lem3628228 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term366 A B s f x) = (term359 A B s f x).
Proof. exact (eq_refl (term366 A B s f x)). Qed.
Lemma lem3628229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628230 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term372 A B s f x) = (term373 A B s f x).
Proof. exact (MK_COMB (@lem3628229) (@lem3628228 A B s f x)). Qed.
Lemma lem3628231 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628232 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term374 A B x f s) = (term375 A B x f s).
Proof. exact (MK_COMB (@lem3628230 A B s f x) (@lem3628231 A B f s)). Qed.
Lemma lem3628233 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term376 A B f s) = (term377 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3628232 A B x f s)). Qed.
Lemma lem3628234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628235 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term365 A B f s) = (term378 A B f s).
Proof. exact (MK_COMB (@lem3628234 A) (@lem3628233 A B f s)). Qed.
Lemma lem3628236 {A B : Type'} (f : A -> B) (s : A -> Prop) : ((term364 A B f s) = (term365 A B f s)) = ((term363 A B f s) = (term378 A B f s)).
Proof. exact (MK_COMB (@lem3628227 A B f s) (@lem3628235 A B f s)). Qed.
Lemma lem3628237 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term363 A B f s) = (term378 A B f s).
Proof. exact (EQ_MP (@lem3628236 A B f s) (@lem3628217 A B f s)). Qed.
Lemma lem3628239 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3628240 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem3628239 A P Q). Qed.
Lemma lem3628241 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term379 A B x f s) = (term380 A B x f s).
Proof. exact (@lem3628240 A (term358 A B s f x) (term40 A B f s)). Qed.
Lemma lem3628242 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term381 A B s f x y) = (term356 A B s f x y).
Proof. exact (eq_refl (term381 A B s f x y)). Qed.
Lemma lem3628243 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term382 A B s f x) = (term358 A B s f x).
Proof. exact (fun_ext (fun y : A => @lem3628242 A B s f x y)). Qed.
Lemma lem3628244 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628245 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term383 A B s f x) = (term359 A B s f x).
Proof. exact (MK_COMB (@lem3628244 A) (@lem3628243 A B s f x)). Qed.
Lemma lem3628246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628247 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term384 A B s f x) = (term373 A B s f x).
Proof. exact (MK_COMB (@lem3628246) (@lem3628245 A B s f x)). Qed.
Lemma lem3628248 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628249 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term379 A B x f s) = (term375 A B x f s).
Proof. exact (MK_COMB (@lem3628247 A B s f x) (@lem3628248 A B f s)). Qed.
Lemma lem3628250 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628251 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term385 A B x f s) = (term386 A B x f s).
Proof. exact (MK_COMB (@lem3628250) (@lem3628249 A B x f s)). Qed.
Lemma lem3628252 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term381 A B s f x y) = (term356 A B s f x y).
Proof. exact (eq_refl (term381 A B s f x y)). Qed.
Lemma lem3628253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628254 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (y : A) : (term387 A B s f x y) = (term388 A B s f x y).
Proof. exact (MK_COMB (@lem3628253) (@lem3628252 A B s f x y)). Qed.
Lemma lem3628255 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term40 A B f s).
Proof. exact (eq_refl (term40 A B f s)). Qed.
Lemma lem3628256 {A B : Type'} (x : A) (y : A) (f : A -> B) (s : A -> Prop) : (term389 A B x y f s) = (term390 A B x y f s).
Proof. exact (MK_COMB (@lem3628254 A B s f x y) (@lem3628255 A B f s)). Qed.
Lemma lem3628257 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term391 A B x f s) = (term392 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3628256 A B x y f s)). Qed.
Lemma lem3628258 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628259 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term380 A B x f s) = (term393 A B x f s).
Proof. exact (MK_COMB (@lem3628258 A) (@lem3628257 A B x f s)). Qed.
Lemma lem3628260 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term379 A B x f s) = (term380 A B x f s)) = ((term375 A B x f s) = (term393 A B x f s)).
Proof. exact (MK_COMB (@lem3628251 A B x f s) (@lem3628259 A B x f s)). Qed.
Lemma lem3628261 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term375 A B x f s) = (term393 A B x f s).
Proof. exact (EQ_MP (@lem3628260 A B x f s) (@lem3628241 A B x f s)). Qed.
Lemma lem3628262 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term377 A B f s) = (term394 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3628261 A B x f s)). Qed.
Lemma lem3628263 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628264 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term378 A B f s) = (term395 A B f s).
Proof. exact (MK_COMB (@lem3628263 A) (@lem3628262 A B f s)). Qed.
Lemma lem3628265 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term363 A B f s) = (term395 A B f s).
Proof. exact (TRANS (@lem3628237 A B f s) (@lem3628264 A B f s)). Qed.
Lemma lem3628266 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term331 A B f s) = (term395 A B f s).
Proof. exact (TRANS (@lem3628213 A B f s) (@lem3628265 A B f s)). Qed.
Lemma lem3628267 {A B : Type'} (f : A -> B) : (term332 A B f) = (term396 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628266 A B f s)). Qed.
Lemma lem3628268 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628269 {A B : Type'} (f : A -> B) : (term333 A B f) = (term397 A B f).
Proof. exact (MK_COMB (@lem3628268 A) (@lem3628267 A B f)). Qed.
Lemma lem3628271 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628272 {A : Type'} (P : type672 A) : (term210 A P) = (term211 A P).
Proof. exact (@lem3628271 (A -> Prop) A P). Qed.
Lemma lem3628273 {A B : Type'} (f : A -> B) : (term398 A B f) = (term399 A B f).
Proof. exact (@lem3628272 A (term400 A B f)). Qed.
Lemma lem3628274 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term401 A B f s) = (term394 A B f s).
Proof. exact (eq_refl (term401 A B f s)). Qed.
Lemma lem3628275 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3628276 {A B : Type'} (f : A -> B) (s : A -> Prop) (x : A) : (term402 A B f s x) = (term403 A B f s x).
Proof. exact (MK_COMB (@lem3628274 A B f s) (@lem3628275 A x)). Qed.
Lemma lem3628277 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term403 A B f s x) = (term393 A B x f s).
Proof. exact (eq_refl (term403 A B f s x)). Qed.
Lemma lem3628278 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term402 A B f s x) = (term393 A B x f s).
Proof. exact (TRANS (@lem3628276 A B f s x) (@lem3628277 A B x f s)). Qed.
Lemma lem3628279 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term394 A B f s).
Proof. exact (fun_ext (fun x : A => @lem3628278 A B x f s)). Qed.
Lemma lem3628280 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628281 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term405 A B f s) = (term395 A B f s).
Proof. exact (MK_COMB (@lem3628280 A) (@lem3628279 A B f s)). Qed.
Lemma lem3628282 {A B : Type'} (f : A -> B) : (term406 A B f) = (term396 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628281 A B f s)). Qed.
Lemma lem3628283 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628284 {A B : Type'} (f : A -> B) : (term398 A B f) = (term397 A B f).
Proof. exact (MK_COMB (@lem3628283 A) (@lem3628282 A B f)). Qed.
Lemma lem3628285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628286 {A B : Type'} (f : A -> B) : (term407 A B f) = (term408 A B f).
Proof. exact (MK_COMB (@lem3628285) (@lem3628284 A B f)). Qed.
Lemma lem3628287 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term401 A B f s) = (term394 A B f s).
Proof. exact (eq_refl (term401 A B f s)). Qed.
Lemma lem3628288 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3628289 {A B : Type'} (f : A -> B) (x : type684 A) (s : A -> Prop) : (term409 A B f x s) = (term410 A B f x s).
Proof. exact (MK_COMB (@lem3628287 A B f s) (@lem3628288 A x s)). Qed.
Lemma lem3628290 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term410 A B f x s) = (term411 A B x f s).
Proof. exact (eq_refl (term410 A B f x s)). Qed.
Lemma lem3628291 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term409 A B f x s) = (term411 A B x f s).
Proof. exact (TRANS (@lem3628289 A B f x s) (@lem3628290 A B x f s)). Qed.
Lemma lem3628292 {A B : Type'} (x : type684 A) (f : A -> B) : (term412 A B f x) = (term413 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628291 A B x f s)). Qed.
Lemma lem3628293 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628294 {A B : Type'} (x : type684 A) (f : A -> B) : (term414 A B f x) = (term415 A B x f).
Proof. exact (MK_COMB (@lem3628293 A) (@lem3628292 A B x f)). Qed.
Lemma lem3628295 {A B : Type'} (f : A -> B) : (term416 A B f) = (term417 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3628294 A B x f)). Qed.
Lemma lem3628296 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3628297 {A B : Type'} (f : A -> B) : (term399 A B f) = (term418 A B f).
Proof. exact (MK_COMB (@lem3628296 A) (@lem3628295 A B f)). Qed.
Lemma lem3628298 {A B : Type'} (f : A -> B) : ((term398 A B f) = (term399 A B f)) = ((term397 A B f) = (term418 A B f)).
Proof. exact (MK_COMB (@lem3628286 A B f) (@lem3628297 A B f)). Qed.
Lemma lem3628299 {A B : Type'} (f : A -> B) : (term397 A B f) = (term418 A B f).
Proof. exact (EQ_MP (@lem3628298 A B f) (@lem3628273 A B f)). Qed.
Lemma lem3628301 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628302 {A : Type'} (P : type672 A) : (term210 A P) = (term211 A P).
Proof. exact (@lem3628301 (A -> Prop) A P). Qed.
Lemma lem3628303 {A B : Type'} (x : type684 A) (f : A -> B) : (term419 A B x f) = (term420 A B x f).
Proof. exact (@lem3628302 A (term421 A B x f)). Qed.
Lemma lem3628304 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term422 A B x f s) = (term423 A B x f s).
Proof. exact (eq_refl (term422 A B x f s)). Qed.
Lemma lem3628305 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3628306 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) (y : A) : (term424 A B x f s y) = (term425 A B x f s y).
Proof. exact (MK_COMB (@lem3628304 A B x f s) (@lem3628305 A y)). Qed.
Lemma lem3628307 {A B : Type'} (x : type684 A) (y : A) (f : A -> B) (s : A -> Prop) : (term425 A B x f s y) = (term426 A B x y f s).
Proof. exact (eq_refl (term425 A B x f s y)). Qed.
Lemma lem3628308 {A B : Type'} (x : type684 A) (y : A) (f : A -> B) (s : A -> Prop) : (term424 A B x f s y) = (term426 A B x y f s).
Proof. exact (TRANS (@lem3628306 A B x f s y) (@lem3628307 A B x y f s)). Qed.
Lemma lem3628309 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term427 A B x f s) = (term423 A B x f s).
Proof. exact (fun_ext (fun y : A => @lem3628308 A B x y f s)). Qed.
Lemma lem3628310 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3628311 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term428 A B x f s) = (term411 A B x f s).
Proof. exact (MK_COMB (@lem3628310 A) (@lem3628309 A B x f s)). Qed.
Lemma lem3628312 {A B : Type'} (x : type684 A) (f : A -> B) : (term429 A B x f) = (term413 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628311 A B x f s)). Qed.
Lemma lem3628313 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628314 {A B : Type'} (x : type684 A) (f : A -> B) : (term419 A B x f) = (term415 A B x f).
Proof. exact (MK_COMB (@lem3628313 A) (@lem3628312 A B x f)). Qed.
Lemma lem3628315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628316 {A B : Type'} (x : type684 A) (f : A -> B) : (term430 A B x f) = (term431 A B x f).
Proof. exact (MK_COMB (@lem3628315) (@lem3628314 A B x f)). Qed.
Lemma lem3628317 {A B : Type'} (x : type684 A) (f : A -> B) (s : A -> Prop) : (term422 A B x f s) = (term423 A B x f s).
Proof. exact (eq_refl (term422 A B x f s)). Qed.
Lemma lem3628318 {A : Type'} (y : type684 A) (s : A -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3628319 {A B : Type'} (x : type684 A) (f : A -> B) (y : type684 A) (s : A -> Prop) : (term432 A B x f y s) = (term433 A B x f y s).
Proof. exact (MK_COMB (@lem3628317 A B x f s) (@lem3628318 A y s)). Qed.
Lemma lem3628320 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) (s : A -> Prop) : (term433 A B x f y s) = (term434 A B x y f s).
Proof. exact (eq_refl (term433 A B x f y s)). Qed.
Lemma lem3628321 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) (s : A -> Prop) : (term432 A B x f y s) = (term434 A B x y f s).
Proof. exact (TRANS (@lem3628319 A B x f y s) (@lem3628320 A B x y f s)). Qed.
Lemma lem3628322 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) : (term435 A B x f y) = (term436 A B x y f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3628321 A B x y f s)). Qed.
Lemma lem3628323 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3628324 {A B : Type'} (x : type684 A) (y : type684 A) (f : A -> B) : (term437 A B x f y) = (term438 A B x y f).
Proof. exact (MK_COMB (@lem3628323 A) (@lem3628322 A B x y f)). Qed.
Lemma lem3628325 {A B : Type'} (x : type684 A) (f : A -> B) : (term439 A B x f) = (term440 A B x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3628324 A B x y f)). Qed.
Lemma lem3628326 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3628327 {A B : Type'} (x : type684 A) (f : A -> B) : (term420 A B x f) = (term441 A B x f).
Proof. exact (MK_COMB (@lem3628326 A) (@lem3628325 A B x f)). Qed.
Lemma lem3628328 {A B : Type'} (x : type684 A) (f : A -> B) : ((term419 A B x f) = (term420 A B x f)) = ((term415 A B x f) = (term441 A B x f)).
Proof. exact (MK_COMB (@lem3628316 A B x f) (@lem3628327 A B x f)). Qed.
Lemma lem3628329 {A B : Type'} (x : type684 A) (f : A -> B) : (term415 A B x f) = (term441 A B x f).
Proof. exact (EQ_MP (@lem3628328 A B x f) (@lem3628303 A B x f)). Qed.
Lemma lem3628330 {A B : Type'} (f : A -> B) : (term417 A B f) = (term442 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3628329 A B x f)). Qed.
Lemma lem3628331 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3628332 {A B : Type'} (f : A -> B) : (term418 A B f) = (term443 A B f).
Proof. exact (MK_COMB (@lem3628331 A) (@lem3628330 A B f)). Qed.
Lemma lem3628333 {A B : Type'} (f : A -> B) : (term397 A B f) = (term443 A B f).
Proof. exact (TRANS (@lem3628299 A B f) (@lem3628332 A B f)). Qed.
Lemma lem3628334 {A B : Type'} (f : A -> B) : (term333 A B f) = (term443 A B f).
Proof. exact (TRANS (@lem3628269 A B f) (@lem3628333 A B f)). Qed.
Lemma lem3628335 {A B : Type'} : (term334 A B) = (term444 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3628334 A B f)). Qed.
Lemma lem3628336 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628337 {A B : Type'} : (term335 A B) = (term445 A B).
Proof. exact (MK_COMB (@lem3628336 A B) (@lem3628335 A B)). Qed.
Lemma lem3628339 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628340 {A B : Type'} (P : type503 A B) : (term446 A B P) = (term447 A B P).
Proof. exact (@lem3628339 (A -> B) (type684 A) P). Qed.
Lemma lem3628341 {A B : Type'} : (term448 A B) = (term449 A B).
Proof. exact (@lem3628340 A B (term450 A B)). Qed.
Lemma lem3628342 {A B : Type'} (f : A -> B) : (term451 A B f) = (term442 A B f).
Proof. exact (eq_refl (term451 A B f)). Qed.
Lemma lem3628343 {A : Type'} (x : type684 A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3628344 {A B : Type'} (f : A -> B) (x : type684 A) : (term452 A B f x) = (term453 A B f x).
Proof. exact (MK_COMB (@lem3628342 A B f) (@lem3628343 A x)). Qed.
Lemma lem3628345 {A B : Type'} (x : type684 A) (f : A -> B) : (term453 A B f x) = (term441 A B x f).
Proof. exact (eq_refl (term453 A B f x)). Qed.
Lemma lem3628346 {A B : Type'} (x : type684 A) (f : A -> B) : (term452 A B f x) = (term441 A B x f).
Proof. exact (TRANS (@lem3628344 A B f x) (@lem3628345 A B x f)). Qed.
Lemma lem3628347 {A B : Type'} (f : A -> B) : (term454 A B f) = (term442 A B f).
Proof. exact (fun_ext (fun x : type684 A => @lem3628346 A B x f)). Qed.
Lemma lem3628348 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3628349 {A B : Type'} (f : A -> B) : (term455 A B f) = (term443 A B f).
Proof. exact (MK_COMB (@lem3628348 A) (@lem3628347 A B f)). Qed.
Lemma lem3628350 {A B : Type'} : (term456 A B) = (term444 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3628349 A B f)). Qed.
Lemma lem3628351 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628352 {A B : Type'} : (term448 A B) = (term445 A B).
Proof. exact (MK_COMB (@lem3628351 A B) (@lem3628350 A B)). Qed.
Lemma lem3628353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628354 {A B : Type'} : (term457 A B) = (term458 A B).
Proof. exact (MK_COMB (@lem3628353) (@lem3628352 A B)). Qed.
Lemma lem3628355 {A B : Type'} (f : A -> B) : (term451 A B f) = (term442 A B f).
Proof. exact (eq_refl (term451 A B f)). Qed.
Lemma lem3628356 {A B : Type'} (x : type529 A B) (f : A -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3628357 {A B : Type'} (x : type529 A B) (f : A -> B) : (term459 A B x f) = (term460 A B x f).
Proof. exact (MK_COMB (@lem3628355 A B f) (@lem3628356 A B x f)). Qed.
Lemma lem3628358 {A B : Type'} (x : type529 A B) (f : A -> B) : (term460 A B x f) = (term461 A B x f).
Proof. exact (eq_refl (term460 A B x f)). Qed.
Lemma lem3628359 {A B : Type'} (x : type529 A B) (f : A -> B) : (term459 A B x f) = (term461 A B x f).
Proof. exact (TRANS (@lem3628357 A B x f) (@lem3628358 A B x f)). Qed.
Lemma lem3628360 {A B : Type'} (x : type529 A B) : (term462 A B x) = (term463 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3628359 A B x f)). Qed.
Lemma lem3628361 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628362 {A B : Type'} (x : type529 A B) : (term464 A B x) = (term465 A B x).
Proof. exact (MK_COMB (@lem3628361 A B) (@lem3628360 A B x)). Qed.
Lemma lem3628363 {A B : Type'} : (term466 A B) = (term467 A B).
Proof. exact (fun_ext (fun x : type529 A B => @lem3628362 A B x)). Qed.
Lemma lem3628364 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3628365 {A B : Type'} : (term449 A B) = (term468 A B).
Proof. exact (MK_COMB (@lem3628364 A B) (@lem3628363 A B)). Qed.
Lemma lem3628366 {A B : Type'} : ((term448 A B) = (term449 A B)) = ((term445 A B) = (term468 A B)).
Proof. exact (MK_COMB (@lem3628354 A B) (@lem3628365 A B)). Qed.
Lemma lem3628367 {A B : Type'} : (term445 A B) = (term468 A B).
Proof. exact (EQ_MP (@lem3628366 A B) (@lem3628341 A B)). Qed.
Lemma lem3628369 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628370 {A B : Type'} (P : type503 A B) : (term446 A B P) = (term447 A B P).
Proof. exact (@lem3628369 (A -> B) (type684 A) P). Qed.
Lemma lem3628371 {A B : Type'} (x : type529 A B) : (term469 A B x) = (term470 A B x).
Proof. exact (@lem3628370 A B (term471 A B x)). Qed.
Lemma lem3628372 {A B : Type'} (x : type529 A B) (f : A -> B) : (term472 A B x f) = (term473 A B x f).
Proof. exact (eq_refl (term472 A B x f)). Qed.
Lemma lem3628373 {A : Type'} (y : type684 A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3628374 {A B : Type'} (x : type529 A B) (f : A -> B) (y : type684 A) : (term474 A B x f y) = (term475 A B x f y).
Proof. exact (MK_COMB (@lem3628372 A B x f) (@lem3628373 A y)). Qed.
Lemma lem3628375 {A B : Type'} (x : type529 A B) (y : type684 A) (f : A -> B) : (term475 A B x f y) = (term476 A B x y f).
Proof. exact (eq_refl (term475 A B x f y)). Qed.
Lemma lem3628376 {A B : Type'} (x : type529 A B) (y : type684 A) (f : A -> B) : (term474 A B x f y) = (term476 A B x y f).
Proof. exact (TRANS (@lem3628374 A B x f y) (@lem3628375 A B x y f)). Qed.
Lemma lem3628377 {A B : Type'} (x : type529 A B) (f : A -> B) : (term477 A B x f) = (term473 A B x f).
Proof. exact (fun_ext (fun y : type684 A => @lem3628376 A B x y f)). Qed.
Lemma lem3628378 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3628379 {A B : Type'} (x : type529 A B) (f : A -> B) : (term478 A B x f) = (term461 A B x f).
Proof. exact (MK_COMB (@lem3628378 A) (@lem3628377 A B x f)). Qed.
Lemma lem3628380 {A B : Type'} (x : type529 A B) : (term479 A B x) = (term463 A B x).
Proof. exact (fun_ext (fun f : A -> B => @lem3628379 A B x f)). Qed.
Lemma lem3628381 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628382 {A B : Type'} (x : type529 A B) : (term469 A B x) = (term465 A B x).
Proof. exact (MK_COMB (@lem3628381 A B) (@lem3628380 A B x)). Qed.
Lemma lem3628383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628384 {A B : Type'} (x : type529 A B) : (term480 A B x) = (term481 A B x).
Proof. exact (MK_COMB (@lem3628383) (@lem3628382 A B x)). Qed.
Lemma lem3628385 {A B : Type'} (x : type529 A B) (f : A -> B) : (term472 A B x f) = (term473 A B x f).
Proof. exact (eq_refl (term472 A B x f)). Qed.
Lemma lem3628386 {A B : Type'} (y : type529 A B) (f : A -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3628387 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term482 A B x y f) = (term483 A B x y f).
Proof. exact (MK_COMB (@lem3628385 A B x f) (@lem3628386 A B y f)). Qed.
Lemma lem3628388 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term483 A B x y f) = (term484 A B x y f).
Proof. exact (eq_refl (term483 A B x y f)). Qed.
Lemma lem3628389 {A B : Type'} (x : type529 A B) (y : type529 A B) (f : A -> B) : (term482 A B x y f) = (term484 A B x y f).
Proof. exact (TRANS (@lem3628387 A B x y f) (@lem3628388 A B x y f)). Qed.
Lemma lem3628390 {A B : Type'} (x : type529 A B) (y : type529 A B) : (term485 A B x y) = (term486 A B x y).
Proof. exact (fun_ext (fun f : A -> B => @lem3628389 A B x y f)). Qed.
Lemma lem3628391 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3628392 {A B : Type'} (x : type529 A B) (y : type529 A B) : (term487 A B x y) = (term488 A B x y).
Proof. exact (MK_COMB (@lem3628391 A B) (@lem3628390 A B x y)). Qed.
Lemma lem3628393 {A B : Type'} (x : type529 A B) : (term489 A B x) = (term490 A B x).
Proof. exact (fun_ext (fun y : type529 A B => @lem3628392 A B x y)). Qed.
Lemma lem3628394 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3628395 {A B : Type'} (x : type529 A B) : (term470 A B x) = (term491 A B x).
Proof. exact (MK_COMB (@lem3628394 A B) (@lem3628393 A B x)). Qed.
Lemma lem3628396 {A B : Type'} (x : type529 A B) : ((term469 A B x) = (term470 A B x)) = ((term465 A B x) = (term491 A B x)).
Proof. exact (MK_COMB (@lem3628384 A B x) (@lem3628395 A B x)). Qed.
Lemma lem3628397 {A B : Type'} (x : type529 A B) : (term465 A B x) = (term491 A B x).
Proof. exact (EQ_MP (@lem3628396 A B x) (@lem3628371 A B x)). Qed.
Lemma lem3628398 {A B : Type'} : (term467 A B) = (term492 A B).
Proof. exact (fun_ext (fun x : type529 A B => @lem3628397 A B x)). Qed.
Lemma lem3628399 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> A)) = (@ex ((A -> B) -> (A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> A))). Qed.
Lemma lem3628400 {A B : Type'} : (term468 A B) = (term493 A B).
Proof. exact (MK_COMB (@lem3628399 A B) (@lem3628398 A B)). Qed.
Lemma lem3628401 {A B : Type'} : (term445 A B) = (term493 A B).
Proof. exact (TRANS (@lem3628367 A B) (@lem3628400 A B)). Qed.
Lemma lem3628403 {A B : Type'} : (term335 A B) = (term493 A B).
Proof. exact (TRANS (@lem3628337 A B) (@lem3628401 A B)). Qed.
Lemma lem3628404 {A B : Type'} : (term11 A B) = (term493 A B).
Proof. exact (TRANS (@lem3628060 A B) (@lem3628403 A B)). Qed.
Lemma lem3628405 {A B : Type'} (h1 : term11 A B) : term493 A B.
Proof. exact (EQ_MP (@lem3628404 A B) (@lem3627408 A B h1)). Qed.
Lemma lem3628421 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term110 B s f x y) = (term111 B s f x y).
Proof. exact (@lem17362 (term112 B s x f y) (x = y)). Qed.
Lemma lem3628422 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3628423 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term115 B s f x) = (term116 B s f x).
Proof. exact (@lem3628422 B (term29 B s f x)). Qed.
Lemma lem3628424 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term117 B s f x y) = (term28 B s f x y).
Proof. exact (eq_refl (term117 B s f x y)). Qed.
Lemma lem3628425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3628426 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term118 B s f x y) = (term110 B s f x y).
Proof. exact (MK_COMB (@lem3628425) (@lem3628424 B s f x y)). Qed.
Lemma lem3628427 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term118 B s f x y) = (term111 B s f x y).
Proof. exact (TRANS (@lem3628426 B s f x y) (@lem3628421 B s f x y)). Qed.
Lemma lem3628428 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term119 B s f x) = (term120 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3628427 B s f x y)). Qed.
Lemma lem3628429 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628430 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term116 B s f x) = (term121 B s f x).
Proof. exact (MK_COMB (@lem3628429 B) (@lem3628428 B s f x)). Qed.
Lemma lem3628431 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term115 B s f x) = (term121 B s f x).
Proof. exact (TRANS (@lem3628423 B s f x) (@lem3628430 B s f x)). Qed.
Lemma lem3628432 {B : Type'} (P : B -> Prop) : (term113 B P) = (term114 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3628433 {B : Type'} (s : B -> Prop) (f : B -> B) : (term122 B s f) = (term123 B s f).
Proof. exact (@lem3628432 B (term31 B s f)). Qed.
Lemma lem3628434 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term124 B s f x) = (term30 B s f x).
Proof. exact (eq_refl (term124 B s f x)). Qed.
Lemma lem3628435 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3628436 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term125 B s f x) = (term115 B s f x).
Proof. exact (MK_COMB (@lem3628435) (@lem3628434 B s f x)). Qed.
Lemma lem3628437 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term125 B s f x) = (term121 B s f x).
Proof. exact (TRANS (@lem3628436 B s f x) (@lem3628431 B s f x)). Qed.
Lemma lem3628438 {B : Type'} (s : B -> Prop) (f : B -> B) : (term126 B s f) = (term127 B s f).
Proof. exact (fun_ext (fun x : B => @lem3628437 B s f x)). Qed.
Lemma lem3628439 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628440 {B : Type'} (s : B -> Prop) (f : B -> B) : (term123 B s f) = (term128 B s f).
Proof. exact (MK_COMB (@lem3628439 B) (@lem3628438 B s f)). Qed.
Lemma lem3628441 {B : Type'} (s : B -> Prop) (f : B -> B) : (term122 B s f) = (term128 B s f).
Proof. exact (TRANS (@lem3628433 B s f) (@lem3628440 B s f)). Qed.
Lemma lem3628443 {B : Type'} (s : B -> Prop) : (term129 B s) = (term129 B s).
Proof. exact (eq_refl (term129 B s)). Qed.
Lemma lem3628444 {B : Type'} (s : B -> Prop) (f : B -> B) : (term130 B s f) = (term131 B s f).
Proof. exact (MK_COMB (@lem3628443 B s) (@lem3628441 B s f)). Qed.
Lemma lem3628445 {B : Type'} (s : B -> Prop) (f : B -> B) : (term132 B s f) = (term130 B s f).
Proof. exact (@lem17045 (@INFINITE B s) (term32 B s f)). Qed.
Lemma lem3628446 {B : Type'} (s : B -> Prop) (f : B -> B) : (term132 B s f) = (term131 B s f).
Proof. exact (TRANS (@lem3628445 B s f) (@lem3628444 B s f)). Qed.
Lemma lem3628447 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628448 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628449 {B : Type'} (s : B -> Prop) (f : B -> B) : (term133 B s f) = (term134 B s f).
Proof. exact (MK_COMB (@lem3628448) (@lem3628446 B s f)). Qed.
Lemma lem3628450 {B : Type'} (f : B -> B) (s : B -> Prop) : (term135 B f s) = (term136 B f s).
Proof. exact (MK_COMB (@lem3628449 B s f) (@lem3628447 B f s)). Qed.
Lemma lem3628451 {B : Type'} (f : B -> B) (s : B -> Prop) : (term36 B f s) = (term135 B f s).
Proof. exact (@lem17265 (term34 B s f) (term27 B f s)). Qed.
Lemma lem3628452 {B : Type'} (f : B -> B) (s : B -> Prop) : (term36 B f s) = (term136 B f s).
Proof. exact (TRANS (@lem3628451 B f s) (@lem3628450 B f s)). Qed.
Lemma lem3628453 {B : Type'} (f : B -> B) : (term37 B f) = (term137 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628452 B f s)). Qed.
Lemma lem3628454 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628455 {B : Type'} (f : B -> B) : (term38 B f) = (term138 B f).
Proof. exact (MK_COMB (@lem3628454 B) (@lem3628453 B f)). Qed.
Lemma lem3628456 {B : Type'} : (term39 B) = (term139 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3628455 B f)). Qed.
Lemma lem3628457 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628458 {B : Type'} : (term12 B) = (term140 B).
Proof. exact (MK_COMB (@lem3628457 B) (@lem3628456 B)). Qed.
Lemma lem3628565 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3628566 {B : Type'} (P : Prop) (Q : B -> Prop) : (term141 B P Q) = (term142 B P Q).
Proof. exact (@lem3628565 B P Q). Qed.
Lemma lem3628567 {B : Type'} (s : B -> Prop) (f : B -> B) : (term143 B s f) = (term144 B s f).
Proof. exact (@lem3628566 B (term145 B s) (term127 B s f)). Qed.
Lemma lem3628568 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term146 B s f x) = (term121 B s f x).
Proof. exact (eq_refl (term146 B s f x)). Qed.
Lemma lem3628569 {B : Type'} (s : B -> Prop) (f : B -> B) : (term147 B s f) = (term127 B s f).
Proof. exact (fun_ext (fun x : B => @lem3628568 B s f x)). Qed.
Lemma lem3628570 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628571 {B : Type'} (s : B -> Prop) (f : B -> B) : (term148 B s f) = (term128 B s f).
Proof. exact (MK_COMB (@lem3628570 B) (@lem3628569 B s f)). Qed.
Lemma lem3628572 {B : Type'} (s : B -> Prop) : (term129 B s) = (term129 B s).
Proof. exact (eq_refl (term129 B s)). Qed.
Lemma lem3628573 {B : Type'} (s : B -> Prop) (f : B -> B) : (term143 B s f) = (term131 B s f).
Proof. exact (MK_COMB (@lem3628572 B s) (@lem3628571 B s f)). Qed.
Lemma lem3628574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628575 {B : Type'} (s : B -> Prop) (f : B -> B) : (term149 B s f) = (term150 B s f).
Proof. exact (MK_COMB (@lem3628574) (@lem3628573 B s f)). Qed.
Lemma lem3628576 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term146 B s f x) = (term121 B s f x).
Proof. exact (eq_refl (term146 B s f x)). Qed.
Lemma lem3628577 {B : Type'} (s : B -> Prop) : (term129 B s) = (term129 B s).
Proof. exact (eq_refl (term129 B s)). Qed.
Lemma lem3628578 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term151 B s f x) = (term152 B s f x).
Proof. exact (MK_COMB (@lem3628577 B s) (@lem3628576 B s f x)). Qed.
Lemma lem3628579 {B : Type'} (s : B -> Prop) (f : B -> B) : (term153 B s f) = (term154 B s f).
Proof. exact (fun_ext (fun x : B => @lem3628578 B s f x)). Qed.
Lemma lem3628580 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628581 {B : Type'} (s : B -> Prop) (f : B -> B) : (term144 B s f) = (term155 B s f).
Proof. exact (MK_COMB (@lem3628580 B) (@lem3628579 B s f)). Qed.
Lemma lem3628582 {B : Type'} (s : B -> Prop) (f : B -> B) : ((term143 B s f) = (term144 B s f)) = ((term131 B s f) = (term155 B s f)).
Proof. exact (MK_COMB (@lem3628575 B s f) (@lem3628581 B s f)). Qed.
Lemma lem3628583 {B : Type'} (s : B -> Prop) (f : B -> B) : (term131 B s f) = (term155 B s f).
Proof. exact (EQ_MP (@lem3628582 B s f) (@lem3628567 B s f)). Qed.
Lemma lem3628585 {A : Type'} (P : Prop) (Q : A -> Prop) : (term141 A P Q) = (term142 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3628586 {B : Type'} (P : Prop) (Q : B -> Prop) : (term141 B P Q) = (term142 B P Q).
Proof. exact (@lem3628585 B P Q). Qed.
Lemma lem3628587 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term156 B s f x) = (term157 B s f x).
Proof. exact (@lem3628586 B (term145 B s) (term120 B s f x)). Qed.
Lemma lem3628588 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term158 B s f x y) = (term111 B s f x y).
Proof. exact (eq_refl (term158 B s f x y)). Qed.
Lemma lem3628589 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term159 B s f x) = (term120 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3628588 B s f x y)). Qed.
Lemma lem3628590 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628591 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term160 B s f x) = (term121 B s f x).
Proof. exact (MK_COMB (@lem3628590 B) (@lem3628589 B s f x)). Qed.
Lemma lem3628592 {B : Type'} (s : B -> Prop) : (term129 B s) = (term129 B s).
Proof. exact (eq_refl (term129 B s)). Qed.
Lemma lem3628593 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term156 B s f x) = (term152 B s f x).
Proof. exact (MK_COMB (@lem3628592 B s) (@lem3628591 B s f x)). Qed.
Lemma lem3628594 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628595 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term161 B s f x) = (term162 B s f x).
Proof. exact (MK_COMB (@lem3628594) (@lem3628593 B s f x)). Qed.
Lemma lem3628596 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term158 B s f x y) = (term111 B s f x y).
Proof. exact (eq_refl (term158 B s f x y)). Qed.
Lemma lem3628597 {B : Type'} (s : B -> Prop) : (term129 B s) = (term129 B s).
Proof. exact (eq_refl (term129 B s)). Qed.
Lemma lem3628598 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term163 B s f x y) = (term164 B s f x y).
Proof. exact (MK_COMB (@lem3628597 B s) (@lem3628596 B s f x y)). Qed.
Lemma lem3628599 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term165 B s f x) = (term166 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3628598 B s f x y)). Qed.
Lemma lem3628600 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628601 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term157 B s f x) = (term167 B s f x).
Proof. exact (MK_COMB (@lem3628600 B) (@lem3628599 B s f x)). Qed.
Lemma lem3628602 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : ((term156 B s f x) = (term157 B s f x)) = ((term152 B s f x) = (term167 B s f x)).
Proof. exact (MK_COMB (@lem3628595 B s f x) (@lem3628601 B s f x)). Qed.
Lemma lem3628603 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term152 B s f x) = (term167 B s f x).
Proof. exact (EQ_MP (@lem3628602 B s f x) (@lem3628587 B s f x)). Qed.
Lemma lem3628604 {B : Type'} (s : B -> Prop) (f : B -> B) : (term154 B s f) = (term168 B s f).
Proof. exact (fun_ext (fun x : B => @lem3628603 B s f x)). Qed.
Lemma lem3628605 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628606 {B : Type'} (s : B -> Prop) (f : B -> B) : (term155 B s f) = (term169 B s f).
Proof. exact (MK_COMB (@lem3628605 B) (@lem3628604 B s f)). Qed.
Lemma lem3628607 {B : Type'} (s : B -> Prop) (f : B -> B) : (term131 B s f) = (term169 B s f).
Proof. exact (TRANS (@lem3628583 B s f) (@lem3628606 B s f)). Qed.
Lemma lem3628608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628609 {B : Type'} (s : B -> Prop) (f : B -> B) : (term134 B s f) = (term170 B s f).
Proof. exact (MK_COMB (@lem3628608) (@lem3628607 B s f)). Qed.
Lemma lem3628610 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628611 {B : Type'} (f : B -> B) (s : B -> Prop) : (term136 B f s) = (term171 B f s).
Proof. exact (MK_COMB (@lem3628609 B s f) (@lem3628610 B f s)). Qed.
Lemma lem3628613 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3628614 {B : Type'} (P : B -> Prop) (Q : Prop) : (term172 B P Q) = (term173 B P Q).
Proof. exact (@lem3628613 B P Q). Qed.
Lemma lem3628615 {B : Type'} (f : B -> B) (s : B -> Prop) : (term174 B f s) = (term175 B f s).
Proof. exact (@lem3628614 B (term168 B s f) (term27 B f s)). Qed.
Lemma lem3628616 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term176 B s f x) = (term167 B s f x).
Proof. exact (eq_refl (term176 B s f x)). Qed.
Lemma lem3628617 {B : Type'} (s : B -> Prop) (f : B -> B) : (term177 B s f) = (term168 B s f).
Proof. exact (fun_ext (fun x : B => @lem3628616 B s f x)). Qed.
Lemma lem3628618 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628619 {B : Type'} (s : B -> Prop) (f : B -> B) : (term178 B s f) = (term169 B s f).
Proof. exact (MK_COMB (@lem3628618 B) (@lem3628617 B s f)). Qed.
Lemma lem3628620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628621 {B : Type'} (s : B -> Prop) (f : B -> B) : (term179 B s f) = (term170 B s f).
Proof. exact (MK_COMB (@lem3628620) (@lem3628619 B s f)). Qed.
Lemma lem3628622 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628623 {B : Type'} (f : B -> B) (s : B -> Prop) : (term174 B f s) = (term171 B f s).
Proof. exact (MK_COMB (@lem3628621 B s f) (@lem3628622 B f s)). Qed.
Lemma lem3628624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628625 {B : Type'} (f : B -> B) (s : B -> Prop) : (term180 B f s) = (term181 B f s).
Proof. exact (MK_COMB (@lem3628624) (@lem3628623 B f s)). Qed.
Lemma lem3628626 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term176 B s f x) = (term167 B s f x).
Proof. exact (eq_refl (term176 B s f x)). Qed.
Lemma lem3628627 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628628 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term182 B s f x) = (term183 B s f x).
Proof. exact (MK_COMB (@lem3628627) (@lem3628626 B s f x)). Qed.
Lemma lem3628629 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628630 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term184 B x f s) = (term185 B x f s).
Proof. exact (MK_COMB (@lem3628628 B s f x) (@lem3628629 B f s)). Qed.
Lemma lem3628631 {B : Type'} (f : B -> B) (s : B -> Prop) : (term186 B f s) = (term187 B f s).
Proof. exact (fun_ext (fun x : B => @lem3628630 B x f s)). Qed.
Lemma lem3628632 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628633 {B : Type'} (f : B -> B) (s : B -> Prop) : (term175 B f s) = (term188 B f s).
Proof. exact (MK_COMB (@lem3628632 B) (@lem3628631 B f s)). Qed.
Lemma lem3628634 {B : Type'} (f : B -> B) (s : B -> Prop) : ((term174 B f s) = (term175 B f s)) = ((term171 B f s) = (term188 B f s)).
Proof. exact (MK_COMB (@lem3628625 B f s) (@lem3628633 B f s)). Qed.
Lemma lem3628635 {B : Type'} (f : B -> B) (s : B -> Prop) : (term171 B f s) = (term188 B f s).
Proof. exact (EQ_MP (@lem3628634 B f s) (@lem3628615 B f s)). Qed.
Lemma lem3628637 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3628638 {B : Type'} (P : B -> Prop) (Q : Prop) : (term172 B P Q) = (term173 B P Q).
Proof. exact (@lem3628637 B P Q). Qed.
Lemma lem3628639 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term189 B x f s) = (term190 B x f s).
Proof. exact (@lem3628638 B (term166 B s f x) (term27 B f s)). Qed.
Lemma lem3628640 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term191 B s f x y) = (term164 B s f x y).
Proof. exact (eq_refl (term191 B s f x y)). Qed.
Lemma lem3628641 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term192 B s f x) = (term166 B s f x).
Proof. exact (fun_ext (fun y : B => @lem3628640 B s f x y)). Qed.
Lemma lem3628642 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628643 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term193 B s f x) = (term167 B s f x).
Proof. exact (MK_COMB (@lem3628642 B) (@lem3628641 B s f x)). Qed.
Lemma lem3628644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628645 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) : (term194 B s f x) = (term183 B s f x).
Proof. exact (MK_COMB (@lem3628644) (@lem3628643 B s f x)). Qed.
Lemma lem3628646 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628647 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term189 B x f s) = (term185 B x f s).
Proof. exact (MK_COMB (@lem3628645 B s f x) (@lem3628646 B f s)). Qed.
Lemma lem3628648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628649 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term195 B x f s) = (term196 B x f s).
Proof. exact (MK_COMB (@lem3628648) (@lem3628647 B x f s)). Qed.
Lemma lem3628650 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term191 B s f x y) = (term164 B s f x y).
Proof. exact (eq_refl (term191 B s f x y)). Qed.
Lemma lem3628651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3628652 {B : Type'} (s : B -> Prop) (f : B -> B) (x : B) (y : B) : (term197 B s f x y) = (term198 B s f x y).
Proof. exact (MK_COMB (@lem3628651) (@lem3628650 B s f x y)). Qed.
Lemma lem3628653 {B : Type'} (f : B -> B) (s : B -> Prop) : (term27 B f s) = (term27 B f s).
Proof. exact (eq_refl (term27 B f s)). Qed.
Lemma lem3628654 {B : Type'} (x : B) (y : B) (f : B -> B) (s : B -> Prop) : (term199 B x y f s) = (term200 B x y f s).
Proof. exact (MK_COMB (@lem3628652 B s f x y) (@lem3628653 B f s)). Qed.
Lemma lem3628655 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term201 B x f s) = (term202 B x f s).
Proof. exact (fun_ext (fun y : B => @lem3628654 B x y f s)). Qed.
Lemma lem3628656 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628657 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term190 B x f s) = (term203 B x f s).
Proof. exact (MK_COMB (@lem3628656 B) (@lem3628655 B x f s)). Qed.
Lemma lem3628658 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : ((term189 B x f s) = (term190 B x f s)) = ((term185 B x f s) = (term203 B x f s)).
Proof. exact (MK_COMB (@lem3628649 B x f s) (@lem3628657 B x f s)). Qed.
Lemma lem3628659 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term185 B x f s) = (term203 B x f s).
Proof. exact (EQ_MP (@lem3628658 B x f s) (@lem3628639 B x f s)). Qed.
Lemma lem3628660 {B : Type'} (f : B -> B) (s : B -> Prop) : (term187 B f s) = (term204 B f s).
Proof. exact (fun_ext (fun x : B => @lem3628659 B x f s)). Qed.
Lemma lem3628661 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628662 {B : Type'} (f : B -> B) (s : B -> Prop) : (term188 B f s) = (term205 B f s).
Proof. exact (MK_COMB (@lem3628661 B) (@lem3628660 B f s)). Qed.
Lemma lem3628663 {B : Type'} (f : B -> B) (s : B -> Prop) : (term171 B f s) = (term205 B f s).
Proof. exact (TRANS (@lem3628635 B f s) (@lem3628662 B f s)). Qed.
Lemma lem3628664 {B : Type'} (f : B -> B) (s : B -> Prop) : (term136 B f s) = (term205 B f s).
Proof. exact (TRANS (@lem3628611 B f s) (@lem3628663 B f s)). Qed.
Lemma lem3628665 {B : Type'} (f : B -> B) : (term137 B f) = (term206 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628664 B f s)). Qed.
Lemma lem3628666 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628667 {B : Type'} (f : B -> B) : (term138 B f) = (term207 B f).
Proof. exact (MK_COMB (@lem3628666 B) (@lem3628665 B f)). Qed.
Lemma lem3628669 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628670 {B : Type'} (P : type672 B) : (term210 B P) = (term211 B P).
Proof. exact (@lem3628669 (B -> Prop) B P). Qed.
Lemma lem3628671 {B : Type'} (f : B -> B) : (term212 B f) = (term213 B f).
Proof. exact (@lem3628670 B (term214 B f)). Qed.
Lemma lem3628672 {B : Type'} (f : B -> B) (s : B -> Prop) : (term215 B f s) = (term204 B f s).
Proof. exact (eq_refl (term215 B f s)). Qed.
Lemma lem3628673 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3628674 {B : Type'} (f : B -> B) (s : B -> Prop) (x : B) : (term216 B f s x) = (term217 B f s x).
Proof. exact (MK_COMB (@lem3628672 B f s) (@lem3628673 B x)). Qed.
Lemma lem3628675 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term217 B f s x) = (term203 B x f s).
Proof. exact (eq_refl (term217 B f s x)). Qed.
Lemma lem3628676 {B : Type'} (x : B) (f : B -> B) (s : B -> Prop) : (term216 B f s x) = (term203 B x f s).
Proof. exact (TRANS (@lem3628674 B f s x) (@lem3628675 B x f s)). Qed.
Lemma lem3628677 {B : Type'} (f : B -> B) (s : B -> Prop) : (term218 B f s) = (term204 B f s).
Proof. exact (fun_ext (fun x : B => @lem3628676 B x f s)). Qed.
Lemma lem3628678 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628679 {B : Type'} (f : B -> B) (s : B -> Prop) : (term219 B f s) = (term205 B f s).
Proof. exact (MK_COMB (@lem3628678 B) (@lem3628677 B f s)). Qed.
Lemma lem3628680 {B : Type'} (f : B -> B) : (term220 B f) = (term206 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628679 B f s)). Qed.
Lemma lem3628681 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628682 {B : Type'} (f : B -> B) : (term212 B f) = (term207 B f).
Proof. exact (MK_COMB (@lem3628681 B) (@lem3628680 B f)). Qed.
Lemma lem3628683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628684 {B : Type'} (f : B -> B) : (term221 B f) = (term222 B f).
Proof. exact (MK_COMB (@lem3628683) (@lem3628682 B f)). Qed.
Lemma lem3628685 {B : Type'} (f : B -> B) (s : B -> Prop) : (term215 B f s) = (term204 B f s).
Proof. exact (eq_refl (term215 B f s)). Qed.
Lemma lem3628686 {B : Type'} (x : type684 B) (s : B -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3628687 {B : Type'} (f : B -> B) (x : type684 B) (s : B -> Prop) : (term223 B f x s) = (term224 B f x s).
Proof. exact (MK_COMB (@lem3628685 B f s) (@lem3628686 B x s)). Qed.
Lemma lem3628688 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term224 B f x s) = (term225 B x f s).
Proof. exact (eq_refl (term224 B f x s)). Qed.
Lemma lem3628689 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term223 B f x s) = (term225 B x f s).
Proof. exact (TRANS (@lem3628687 B f x s) (@lem3628688 B x f s)). Qed.
Lemma lem3628690 {B : Type'} (x : type684 B) (f : B -> B) : (term226 B f x) = (term227 B x f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628689 B x f s)). Qed.
Lemma lem3628691 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628692 {B : Type'} (x : type684 B) (f : B -> B) : (term228 B f x) = (term229 B x f).
Proof. exact (MK_COMB (@lem3628691 B) (@lem3628690 B x f)). Qed.
Lemma lem3628693 {B : Type'} (f : B -> B) : (term230 B f) = (term231 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem3628692 B x f)). Qed.
Lemma lem3628694 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem3628695 {B : Type'} (f : B -> B) : (term213 B f) = (term232 B f).
Proof. exact (MK_COMB (@lem3628694 B) (@lem3628693 B f)). Qed.
Lemma lem3628696 {B : Type'} (f : B -> B) : ((term212 B f) = (term213 B f)) = ((term207 B f) = (term232 B f)).
Proof. exact (MK_COMB (@lem3628684 B f) (@lem3628695 B f)). Qed.
Lemma lem3628697 {B : Type'} (f : B -> B) : (term207 B f) = (term232 B f).
Proof. exact (EQ_MP (@lem3628696 B f) (@lem3628671 B f)). Qed.
Lemma lem3628699 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628700 {B : Type'} (P : type672 B) : (term210 B P) = (term211 B P).
Proof. exact (@lem3628699 (B -> Prop) B P). Qed.
Lemma lem3628701 {B : Type'} (x : type684 B) (f : B -> B) : (term233 B x f) = (term234 B x f).
Proof. exact (@lem3628700 B (term235 B x f)). Qed.
Lemma lem3628702 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term236 B x f s) = (term237 B x f s).
Proof. exact (eq_refl (term236 B x f s)). Qed.
Lemma lem3628703 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3628704 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) (y : B) : (term238 B x f s y) = (term239 B x f s y).
Proof. exact (MK_COMB (@lem3628702 B x f s) (@lem3628703 B y)). Qed.
Lemma lem3628705 {B : Type'} (x : type684 B) (y : B) (f : B -> B) (s : B -> Prop) : (term239 B x f s y) = (term240 B x y f s).
Proof. exact (eq_refl (term239 B x f s y)). Qed.
Lemma lem3628706 {B : Type'} (x : type684 B) (y : B) (f : B -> B) (s : B -> Prop) : (term238 B x f s y) = (term240 B x y f s).
Proof. exact (TRANS (@lem3628704 B x f s y) (@lem3628705 B x y f s)). Qed.
Lemma lem3628707 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term241 B x f s) = (term237 B x f s).
Proof. exact (fun_ext (fun y : B => @lem3628706 B x y f s)). Qed.
Lemma lem3628708 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3628709 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term242 B x f s) = (term225 B x f s).
Proof. exact (MK_COMB (@lem3628708 B) (@lem3628707 B x f s)). Qed.
Lemma lem3628710 {B : Type'} (x : type684 B) (f : B -> B) : (term243 B x f) = (term227 B x f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628709 B x f s)). Qed.
Lemma lem3628711 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628712 {B : Type'} (x : type684 B) (f : B -> B) : (term233 B x f) = (term229 B x f).
Proof. exact (MK_COMB (@lem3628711 B) (@lem3628710 B x f)). Qed.
Lemma lem3628713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628714 {B : Type'} (x : type684 B) (f : B -> B) : (term244 B x f) = (term245 B x f).
Proof. exact (MK_COMB (@lem3628713) (@lem3628712 B x f)). Qed.
Lemma lem3628715 {B : Type'} (x : type684 B) (f : B -> B) (s : B -> Prop) : (term236 B x f s) = (term237 B x f s).
Proof. exact (eq_refl (term236 B x f s)). Qed.
Lemma lem3628716 {B : Type'} (y : type684 B) (s : B -> Prop) : (y s) = (y s).
Proof. exact (eq_refl (y s)). Qed.
Lemma lem3628717 {B : Type'} (x : type684 B) (f : B -> B) (y : type684 B) (s : B -> Prop) : (term246 B x f y s) = (term247 B x f y s).
Proof. exact (MK_COMB (@lem3628715 B x f s) (@lem3628716 B y s)). Qed.
Lemma lem3628718 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) (s : B -> Prop) : (term247 B x f y s) = (term248 B x y f s).
Proof. exact (eq_refl (term247 B x f y s)). Qed.
Lemma lem3628719 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) (s : B -> Prop) : (term246 B x f y s) = (term248 B x y f s).
Proof. exact (TRANS (@lem3628717 B x f y s) (@lem3628718 B x y f s)). Qed.
Lemma lem3628720 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) : (term249 B x f y) = (term250 B x y f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3628719 B x y f s)). Qed.
Lemma lem3628721 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3628722 {B : Type'} (x : type684 B) (y : type684 B) (f : B -> B) : (term251 B x f y) = (term252 B x y f).
Proof. exact (MK_COMB (@lem3628721 B) (@lem3628720 B x y f)). Qed.
Lemma lem3628723 {B : Type'} (x : type684 B) (f : B -> B) : (term253 B x f) = (term254 B x f).
Proof. exact (fun_ext (fun y : type684 B => @lem3628722 B x y f)). Qed.
Lemma lem3628724 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem3628725 {B : Type'} (x : type684 B) (f : B -> B) : (term234 B x f) = (term255 B x f).
Proof. exact (MK_COMB (@lem3628724 B) (@lem3628723 B x f)). Qed.
Lemma lem3628726 {B : Type'} (x : type684 B) (f : B -> B) : ((term233 B x f) = (term234 B x f)) = ((term229 B x f) = (term255 B x f)).
Proof. exact (MK_COMB (@lem3628714 B x f) (@lem3628725 B x f)). Qed.
Lemma lem3628727 {B : Type'} (x : type684 B) (f : B -> B) : (term229 B x f) = (term255 B x f).
Proof. exact (EQ_MP (@lem3628726 B x f) (@lem3628701 B x f)). Qed.
Lemma lem3628728 {B : Type'} (f : B -> B) : (term231 B f) = (term256 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem3628727 B x f)). Qed.
Lemma lem3628729 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem3628730 {B : Type'} (f : B -> B) : (term232 B f) = (term257 B f).
Proof. exact (MK_COMB (@lem3628729 B) (@lem3628728 B f)). Qed.
Lemma lem3628731 {B : Type'} (f : B -> B) : (term207 B f) = (term257 B f).
Proof. exact (TRANS (@lem3628697 B f) (@lem3628730 B f)). Qed.
Lemma lem3628732 {B : Type'} (f : B -> B) : (term138 B f) = (term257 B f).
Proof. exact (TRANS (@lem3628667 B f) (@lem3628731 B f)). Qed.
Lemma lem3628733 {B : Type'} : (term139 B) = (term258 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3628732 B f)). Qed.
Lemma lem3628734 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628735 {B : Type'} : (term140 B) = (term259 B).
Proof. exact (MK_COMB (@lem3628734 B) (@lem3628733 B)). Qed.
Lemma lem3628737 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628738 {B : Type'} (P : type481 B) : (term260 B P) = (term261 B P).
Proof. exact (@lem3628737 (B -> B) (type684 B) P). Qed.
Lemma lem3628739 {B : Type'} : (term262 B) = (term263 B).
Proof. exact (@lem3628738 B (term264 B)). Qed.
Lemma lem3628740 {B : Type'} (f : B -> B) : (term265 B f) = (term256 B f).
Proof. exact (eq_refl (term265 B f)). Qed.
Lemma lem3628741 {B : Type'} (x : type684 B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3628742 {B : Type'} (f : B -> B) (x : type684 B) : (term266 B f x) = (term267 B f x).
Proof. exact (MK_COMB (@lem3628740 B f) (@lem3628741 B x)). Qed.
Lemma lem3628743 {B : Type'} (x : type684 B) (f : B -> B) : (term267 B f x) = (term255 B x f).
Proof. exact (eq_refl (term267 B f x)). Qed.
Lemma lem3628744 {B : Type'} (x : type684 B) (f : B -> B) : (term266 B f x) = (term255 B x f).
Proof. exact (TRANS (@lem3628742 B f x) (@lem3628743 B x f)). Qed.
Lemma lem3628745 {B : Type'} (f : B -> B) : (term268 B f) = (term256 B f).
Proof. exact (fun_ext (fun x : type684 B => @lem3628744 B x f)). Qed.
Lemma lem3628746 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem3628747 {B : Type'} (f : B -> B) : (term269 B f) = (term257 B f).
Proof. exact (MK_COMB (@lem3628746 B) (@lem3628745 B f)). Qed.
Lemma lem3628748 {B : Type'} : (term270 B) = (term258 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3628747 B f)). Qed.
Lemma lem3628749 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628750 {B : Type'} : (term262 B) = (term259 B).
Proof. exact (MK_COMB (@lem3628749 B) (@lem3628748 B)). Qed.
Lemma lem3628751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628752 {B : Type'} : (term271 B) = (term272 B).
Proof. exact (MK_COMB (@lem3628751) (@lem3628750 B)). Qed.
Lemma lem3628753 {B : Type'} (f : B -> B) : (term265 B f) = (term256 B f).
Proof. exact (eq_refl (term265 B f)). Qed.
Lemma lem3628754 {B : Type'} (x : type485 B) (f : B -> B) : (x f) = (x f).
Proof. exact (eq_refl (x f)). Qed.
Lemma lem3628755 {B : Type'} (x : type485 B) (f : B -> B) : (term273 B x f) = (term274 B x f).
Proof. exact (MK_COMB (@lem3628753 B f) (@lem3628754 B x f)). Qed.
Lemma lem3628756 {B : Type'} (x : type485 B) (f : B -> B) : (term274 B x f) = (term275 B x f).
Proof. exact (eq_refl (term274 B x f)). Qed.
Lemma lem3628757 {B : Type'} (x : type485 B) (f : B -> B) : (term273 B x f) = (term275 B x f).
Proof. exact (TRANS (@lem3628755 B x f) (@lem3628756 B x f)). Qed.
Lemma lem3628758 {B : Type'} (x : type485 B) : (term276 B x) = (term277 B x).
Proof. exact (fun_ext (fun f : B -> B => @lem3628757 B x f)). Qed.
Lemma lem3628759 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628760 {B : Type'} (x : type485 B) : (term278 B x) = (term279 B x).
Proof. exact (MK_COMB (@lem3628759 B) (@lem3628758 B x)). Qed.
Lemma lem3628761 {B : Type'} : (term280 B) = (term281 B).
Proof. exact (fun_ext (fun x : type485 B => @lem3628760 B x)). Qed.
Lemma lem3628762 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem3628763 {B : Type'} : (term263 B) = (term282 B).
Proof. exact (MK_COMB (@lem3628762 B) (@lem3628761 B)). Qed.
Lemma lem3628764 {B : Type'} : ((term262 B) = (term263 B)) = ((term259 B) = (term282 B)).
Proof. exact (MK_COMB (@lem3628752 B) (@lem3628763 B)). Qed.
Lemma lem3628765 {B : Type'} : (term259 B) = (term282 B).
Proof. exact (EQ_MP (@lem3628764 B) (@lem3628739 B)). Qed.
Lemma lem3628767 {A B : Type'} (P : type1413 A B) : (term208 A B P) = (term209 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3628768 {B : Type'} (P : type481 B) : (term260 B P) = (term261 B P).
Proof. exact (@lem3628767 (B -> B) (type684 B) P). Qed.
Lemma lem3628769 {B : Type'} (x : type485 B) : (term283 B x) = (term284 B x).
Proof. exact (@lem3628768 B (term285 B x)). Qed.
Lemma lem3628770 {B : Type'} (x : type485 B) (f : B -> B) : (term286 B x f) = (term287 B x f).
Proof. exact (eq_refl (term286 B x f)). Qed.
Lemma lem3628771 {B : Type'} (y : type684 B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3628772 {B : Type'} (x : type485 B) (f : B -> B) (y : type684 B) : (term288 B x f y) = (term289 B x f y).
Proof. exact (MK_COMB (@lem3628770 B x f) (@lem3628771 B y)). Qed.
Lemma lem3628773 {B : Type'} (x : type485 B) (y : type684 B) (f : B -> B) : (term289 B x f y) = (term290 B x y f).
Proof. exact (eq_refl (term289 B x f y)). Qed.
Lemma lem3628774 {B : Type'} (x : type485 B) (y : type684 B) (f : B -> B) : (term288 B x f y) = (term290 B x y f).
Proof. exact (TRANS (@lem3628772 B x f y) (@lem3628773 B x y f)). Qed.
Lemma lem3628775 {B : Type'} (x : type485 B) (f : B -> B) : (term291 B x f) = (term287 B x f).
Proof. exact (fun_ext (fun y : type684 B => @lem3628774 B x y f)). Qed.
Lemma lem3628776 {B : Type'} : (@ex ((B -> Prop) -> B)) = (@ex ((B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B))). Qed.
Lemma lem3628777 {B : Type'} (x : type485 B) (f : B -> B) : (term292 B x f) = (term275 B x f).
Proof. exact (MK_COMB (@lem3628776 B) (@lem3628775 B x f)). Qed.
Lemma lem3628778 {B : Type'} (x : type485 B) : (term293 B x) = (term277 B x).
Proof. exact (fun_ext (fun f : B -> B => @lem3628777 B x f)). Qed.
Lemma lem3628779 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628780 {B : Type'} (x : type485 B) : (term283 B x) = (term279 B x).
Proof. exact (MK_COMB (@lem3628779 B) (@lem3628778 B x)). Qed.
Lemma lem3628781 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3628782 {B : Type'} (x : type485 B) : (term294 B x) = (term295 B x).
Proof. exact (MK_COMB (@lem3628781) (@lem3628780 B x)). Qed.
Lemma lem3628783 {B : Type'} (x : type485 B) (f : B -> B) : (term286 B x f) = (term287 B x f).
Proof. exact (eq_refl (term286 B x f)). Qed.
Lemma lem3628784 {B : Type'} (y : type485 B) (f : B -> B) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem3628785 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term296 B x y f) = (term297 B x y f).
Proof. exact (MK_COMB (@lem3628783 B x f) (@lem3628784 B y f)). Qed.
Lemma lem3628786 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term297 B x y f) = (term298 B x y f).
Proof. exact (eq_refl (term297 B x y f)). Qed.
Lemma lem3628787 {B : Type'} (x : type485 B) (y : type485 B) (f : B -> B) : (term296 B x y f) = (term298 B x y f).
Proof. exact (TRANS (@lem3628785 B x y f) (@lem3628786 B x y f)). Qed.
Lemma lem3628788 {B : Type'} (x : type485 B) (y : type485 B) : (term299 B x y) = (term300 B x y).
Proof. exact (fun_ext (fun f : B -> B => @lem3628787 B x y f)). Qed.
Lemma lem3628789 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3628790 {B : Type'} (x : type485 B) (y : type485 B) : (term301 B x y) = (term302 B x y).
Proof. exact (MK_COMB (@lem3628789 B) (@lem3628788 B x y)). Qed.
Lemma lem3628791 {B : Type'} (x : type485 B) : (term303 B x) = (term304 B x).
Proof. exact (fun_ext (fun y : type485 B => @lem3628790 B x y)). Qed.
Lemma lem3628792 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem3628793 {B : Type'} (x : type485 B) : (term284 B x) = (term305 B x).
Proof. exact (MK_COMB (@lem3628792 B) (@lem3628791 B x)). Qed.
Lemma lem3628794 {B : Type'} (x : type485 B) : ((term283 B x) = (term284 B x)) = ((term279 B x) = (term305 B x)).
Proof. exact (MK_COMB (@lem3628782 B x) (@lem3628793 B x)). Qed.
Lemma lem3628795 {B : Type'} (x : type485 B) : (term279 B x) = (term305 B x).
Proof. exact (EQ_MP (@lem3628794 B x) (@lem3628769 B x)). Qed.
Lemma lem3628796 {B : Type'} : (term281 B) = (term306 B).
Proof. exact (fun_ext (fun x : type485 B => @lem3628795 B x)). Qed.
Lemma lem3628797 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> B)) = (@ex ((B -> B) -> (B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> B))). Qed.
Lemma lem3628798 {B : Type'} : (term282 B) = (term307 B).
Proof. exact (MK_COMB (@lem3628797 B) (@lem3628796 B)). Qed.
Lemma lem3628799 {B : Type'} : (term259 B) = (term307 B).
Proof. exact (TRANS (@lem3628765 B) (@lem3628798 B)). Qed.
Lemma lem3628801 {B : Type'} : (term140 B) = (term307 B).
Proof. exact (TRANS (@lem3628735 B) (@lem3628799 B)). Qed.
Lemma lem3628802 {B : Type'} : (term12 B) = (term307 B).
Proof. exact (TRANS (@lem3628458 B) (@lem3628801 B)). Qed.
Lemma lem3628803 {B : Type'} (h1 : term12 B) : term307 B.
Proof. exact (EQ_MP (@lem3628802 B) (@lem3627409 B h1)). Qed.
Lemma lem3628804 {B : Type'} (x : type485 B) (h1 : term305 B x) : term305 B x.
Proof. exact (h1). Qed.
Lemma lem3628806 {A B : Type'} (x' : type529 A B) (h1 : term491 A B x') : term491 A B x'.
Proof. exact (h1). Qed.
Lemma lem3628807 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term488 A B x' y'.
Proof. exact (h1). Qed.
Lemma lem3628808 {A : Type'} (x'' : type485 A) (h1 : term305 A x'') : term305 A x''.
Proof. exact (h1). Qed.
Lemma lem3628810 {A B : Type'} (f : A -> B) (h1 : term107 A B f) : term107 A B f.
Proof. exact (h1). Qed.
Lemma lem3628811 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term104 A B f s.
Proof. exact (h1). Qed.
Lemma lem3629024 {B : Type'} : (@INFINITE B) = (@INFINITE B).
Proof. exact (eq_refl (@INFINITE B)). Qed.
Lemma lem3629031 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629032 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem3629031 (A -> B) (type678 A B) f x). Qed.
Lemma lem3629033 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem3629032 A B (@IMAGE A B) f). Qed.
Lemma lem3629034 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629035 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem3629033 A B f) (@lem3629034 A s)). Qed.
Lemma lem3629037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629038 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem3629037 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem3629039 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term494 A B f s).
Proof. exact (@lem3629038 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem3629041 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term494 A B f s).
Proof. exact (TRANS (@lem3629035 A B f s) (@lem3629039 A B f s)). Qed.
Lemma lem3629042 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term495 A B f s).
Proof. exact (MK_COMB (@lem3629024 B) (@lem3629041 A B f s)). Qed.
Lemma lem3629044 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629045 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3629044 (B -> Prop) Prop f x). Qed.
Lemma lem3629046 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term495 A B f s) = (term496 A B f s).
Proof. exact (@lem3629045 B (@INFINITE B) (term494 A B f s)). Qed.
Lemma lem3629047 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term496 A B f s).
Proof. exact (TRANS (@lem3629042 A B f s) (@lem3629046 A B f s)). Qed.
Lemma lem3629048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3629049 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem3629056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629057 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629056 (A -> B) (type684 A) f x). Qed.
Lemma lem3629058 {A B : Type'} (x' : type529 A B) (f : A -> B) : (x' f) = (@I ((A -> B) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem3629057 A B x' f). Qed.
Lemma lem3629059 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629060 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x' f s).
Proof. exact (MK_COMB (@lem3629058 A B x' f) (@lem3629059 A s)). Qed.
Lemma lem3629062 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629063 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629062 (A -> Prop) A f x). Qed.
Lemma lem3629064 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x' f s) = (term497 A B x' f s).
Proof. exact (@lem3629063 A (@I ((A -> B) -> (A -> Prop) -> A) x' f) s). Qed.
Lemma lem3629066 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (term497 A B x' f s).
Proof. exact (TRANS (@lem3629060 A B x' f s) (@lem3629064 A B x' f s)). Qed.
Lemma lem3629073 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629074 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629073 (A -> B) (type684 A) f x). Qed.
Lemma lem3629075 {A B : Type'} (y' : type529 A B) (f : A -> B) : (y' f) = (@I ((A -> B) -> (A -> Prop) -> A) y' f).
Proof. exact (@lem3629074 A B y' f). Qed.
Lemma lem3629076 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629077 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y' f s).
Proof. exact (MK_COMB (@lem3629075 A B y' f) (@lem3629076 A s)). Qed.
Lemma lem3629079 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629080 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629079 (A -> Prop) A f x). Qed.
Lemma lem3629081 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y' f s) = (term497 A B y' f s).
Proof. exact (@lem3629080 A (@I ((A -> B) -> (A -> Prop) -> A) y' f) s). Qed.
Lemma lem3629083 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (term497 A B y' f s).
Proof. exact (TRANS (@lem3629077 A B y' f s) (@lem3629081 A B y' f s)). Qed.
Lemma lem3629084 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term498 A B x' f s) = (term499 A B x' f s).
Proof. exact (MK_COMB (@lem3629049 A) (@lem3629066 A B x' f s)). Qed.
Lemma lem3629085 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : ((x' f s) = (y' f s)) = ((term497 A B x' f s) = (term497 A B y' f s)).
Proof. exact (MK_COMB (@lem3629084 A B x' f s) (@lem3629083 A B y' f s)). Qed.
Lemma lem3629086 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term500 A B x' y' f s) = (term501 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629048) (@lem3629085 A B x' y' f s)). Qed.
Lemma lem3629087 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3629088 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3629095 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629096 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629095 (A -> B) (type684 A) f x). Qed.
Lemma lem3629097 {A B : Type'} (x' : type529 A B) (f : A -> B) : (x' f) = (@I ((A -> B) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem3629096 A B x' f). Qed.
Lemma lem3629098 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629099 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x' f s).
Proof. exact (MK_COMB (@lem3629097 A B x' f) (@lem3629098 A s)). Qed.
Lemma lem3629101 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629102 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629101 (A -> Prop) A f x). Qed.
Lemma lem3629103 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x' f s) = (term497 A B x' f s).
Proof. exact (@lem3629102 A (@I ((A -> B) -> (A -> Prop) -> A) x' f) s). Qed.
Lemma lem3629105 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (term497 A B x' f s).
Proof. exact (TRANS (@lem3629099 A B x' f s) (@lem3629103 A B x' f s)). Qed.
Lemma lem3629106 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term502 A B x' f s) = (term503 A B x' f s).
Proof. exact (MK_COMB (@lem3629088 A B f) (@lem3629105 A B x' f s)). Qed.
Lemma lem3629108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3629108 A B f x). Qed.
Lemma lem3629110 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term503 A B x' f s) = (term504 A B x' f s).
Proof. exact (@lem3629109 A B f (term497 A B x' f s)). Qed.
Lemma lem3629111 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term502 A B x' f s) = (term504 A B x' f s).
Proof. exact (TRANS (@lem3629106 A B x' f s) (@lem3629110 A B x' f s)). Qed.
Lemma lem3629112 {A B : Type'} (f : A -> B) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3629119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629120 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629119 (A -> B) (type684 A) f x). Qed.
Lemma lem3629121 {A B : Type'} (y' : type529 A B) (f : A -> B) : (y' f) = (@I ((A -> B) -> (A -> Prop) -> A) y' f).
Proof. exact (@lem3629120 A B y' f). Qed.
Lemma lem3629122 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629123 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y' f s).
Proof. exact (MK_COMB (@lem3629121 A B y' f) (@lem3629122 A s)). Qed.
Lemma lem3629125 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629126 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629125 (A -> Prop) A f x). Qed.
Lemma lem3629127 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y' f s) = (term497 A B y' f s).
Proof. exact (@lem3629126 A (@I ((A -> B) -> (A -> Prop) -> A) y' f) s). Qed.
Lemma lem3629129 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (term497 A B y' f s).
Proof. exact (TRANS (@lem3629123 A B y' f s) (@lem3629127 A B y' f s)). Qed.
Lemma lem3629130 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term502 A B y' f s) = (term503 A B y' f s).
Proof. exact (MK_COMB (@lem3629112 A B f) (@lem3629129 A B y' f s)). Qed.
Lemma lem3629132 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629133 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3629132 A B f x). Qed.
Lemma lem3629134 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term503 A B y' f s) = (term504 A B y' f s).
Proof. exact (@lem3629133 A B f (term497 A B y' f s)). Qed.
Lemma lem3629135 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term502 A B y' f s) = (term504 A B y' f s).
Proof. exact (TRANS (@lem3629130 A B y' f s) (@lem3629134 A B y' f s)). Qed.
Lemma lem3629136 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term505 A B x' f s) = (term506 A B x' f s).
Proof. exact (MK_COMB (@lem3629087 B) (@lem3629111 A B x' f s)). Qed.
Lemma lem3629137 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : ((term502 A B x' f s) = (term502 A B y' f s)) = ((term504 A B x' f s) = (term504 A B y' f s)).
Proof. exact (MK_COMB (@lem3629136 A B x' f s) (@lem3629135 A B y' f s)). Qed.
Lemma lem3629138 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3629145 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629146 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629145 (A -> B) (type684 A) f x). Qed.
Lemma lem3629147 {A B : Type'} (y' : type529 A B) (f : A -> B) : (y' f) = (@I ((A -> B) -> (A -> Prop) -> A) y' f).
Proof. exact (@lem3629146 A B y' f). Qed.
Lemma lem3629148 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629149 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (@I ((A -> B) -> (A -> Prop) -> A) y' f s).
Proof. exact (MK_COMB (@lem3629147 A B y' f) (@lem3629148 A s)). Qed.
Lemma lem3629151 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629152 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629151 (A -> Prop) A f x). Qed.
Lemma lem3629153 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) y' f s) = (term497 A B y' f s).
Proof. exact (@lem3629152 A (@I ((A -> B) -> (A -> Prop) -> A) y' f) s). Qed.
Lemma lem3629155 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (y' f s) = (term497 A B y' f s).
Proof. exact (TRANS (@lem3629149 A B y' f s) (@lem3629153 A B y' f s)). Qed.
Lemma lem3629156 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629157 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term507 A B y' f s) = (term508 A B y' f s).
Proof. exact (MK_COMB (@lem3629138 A) (@lem3629155 A B y' f s)). Qed.
Lemma lem3629158 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term509 A B y' f s) = (term510 A B y' f s).
Proof. exact (MK_COMB (@lem3629157 A B y' f s) (@lem3629156 A s)). Qed.
Lemma lem3629160 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629161 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3629160 A (type686 A) f x). Qed.
Lemma lem3629162 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term508 A B y' f s) = (term511 A B y' f s).
Proof. exact (@lem3629161 A (@IN A) (term497 A B y' f s)). Qed.
Lemma lem3629163 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629164 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term510 A B y' f s) = (term512 A B y' f s).
Proof. exact (MK_COMB (@lem3629162 A B y' f s) (@lem3629163 A s)). Qed.
Lemma lem3629166 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629167 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3629166 (A -> Prop) Prop f x). Qed.
Lemma lem3629168 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term512 A B y' f s) = (term513 A B y' f s).
Proof. exact (@lem3629167 A (term511 A B y' f s) s). Qed.
Lemma lem3629169 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term510 A B y' f s) = (term513 A B y' f s).
Proof. exact (TRANS (@lem3629164 A B y' f s) (@lem3629168 A B y' f s)). Qed.
Lemma lem3629170 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term509 A B y' f s) = (term513 A B y' f s).
Proof. exact (TRANS (@lem3629158 A B y' f s) (@lem3629169 A B y' f s)). Qed.
Lemma lem3629171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629172 {A B : Type'} (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term514 A B y' f s) = (term515 A B y' f s).
Proof. exact (MK_COMB (@lem3629171) (@lem3629170 A B y' f s)). Qed.
Lemma lem3629173 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term516 A B x' y' f s) = (term517 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629172 A B y' f s) (@lem3629137 A B x' y' f s)). Qed.
Lemma lem3629174 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem3629181 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629182 {A B : Type'} (f : type529 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> A) f x).
Proof. exact (@lem3629181 (A -> B) (type684 A) f x). Qed.
Lemma lem3629183 {A B : Type'} (x' : type529 A B) (f : A -> B) : (x' f) = (@I ((A -> B) -> (A -> Prop) -> A) x' f).
Proof. exact (@lem3629182 A B x' f). Qed.
Lemma lem3629184 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629185 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (@I ((A -> B) -> (A -> Prop) -> A) x' f s).
Proof. exact (MK_COMB (@lem3629183 A B x' f) (@lem3629184 A s)). Qed.
Lemma lem3629187 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629188 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem3629187 (A -> Prop) A f x). Qed.
Lemma lem3629189 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> A) x' f s) = (term497 A B x' f s).
Proof. exact (@lem3629188 A (@I ((A -> B) -> (A -> Prop) -> A) x' f) s). Qed.
Lemma lem3629191 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (x' f s) = (term497 A B x' f s).
Proof. exact (TRANS (@lem3629185 A B x' f s) (@lem3629189 A B x' f s)). Qed.
Lemma lem3629192 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629193 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term507 A B x' f s) = (term508 A B x' f s).
Proof. exact (MK_COMB (@lem3629174 A) (@lem3629191 A B x' f s)). Qed.
Lemma lem3629194 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term509 A B x' f s) = (term510 A B x' f s).
Proof. exact (MK_COMB (@lem3629193 A B x' f s) (@lem3629192 A s)). Qed.
Lemma lem3629196 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629197 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem3629196 A (type686 A) f x). Qed.
Lemma lem3629198 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term508 A B x' f s) = (term511 A B x' f s).
Proof. exact (@lem3629197 A (@IN A) (term497 A B x' f s)). Qed.
Lemma lem3629199 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629200 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term510 A B x' f s) = (term512 A B x' f s).
Proof. exact (MK_COMB (@lem3629198 A B x' f s) (@lem3629199 A s)). Qed.
Lemma lem3629202 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629203 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3629202 (A -> Prop) Prop f x). Qed.
Lemma lem3629204 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term512 A B x' f s) = (term513 A B x' f s).
Proof. exact (@lem3629203 A (term511 A B x' f s) s). Qed.
Lemma lem3629205 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term510 A B x' f s) = (term513 A B x' f s).
Proof. exact (TRANS (@lem3629200 A B x' f s) (@lem3629204 A B x' f s)). Qed.
Lemma lem3629206 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term509 A B x' f s) = (term513 A B x' f s).
Proof. exact (TRANS (@lem3629194 A B x' f s) (@lem3629205 A B x' f s)). Qed.
Lemma lem3629207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629208 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term514 A B x' f s) = (term515 A B x' f s).
Proof. exact (MK_COMB (@lem3629207) (@lem3629206 A B x' f s)). Qed.
Lemma lem3629209 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term518 A B x' y' f s) = (term519 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629208 A B x' f s) (@lem3629173 A B x' y' f s)). Qed.
Lemma lem3629210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629211 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term520 A B x' y' f s) = (term521 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629210) (@lem3629209 A B x' y' f s)). Qed.
Lemma lem3629212 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term522 A B x' y' f s) = (term523 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629211 A B x' y' f s) (@lem3629086 A B x' y' f s)). Qed.
Lemma lem3629213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3629218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629219 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3629218 (A -> Prop) Prop f x). Qed.
Lemma lem3629221 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@I ((A -> Prop) -> Prop) (@INFINITE A) s).
Proof. exact (@lem3629219 A (@INFINITE A) s). Qed.
Lemma lem3629222 {A : Type'} (s : A -> Prop) : (term145 A s) = (term524 A s).
Proof. exact (MK_COMB (@lem3629213) (@lem3629221 A s)). Qed.
Lemma lem3629223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3629224 {A : Type'} (s : A -> Prop) : (term129 A s) = (term525 A s).
Proof. exact (MK_COMB (@lem3629223) (@lem3629222 A s)). Qed.
Lemma lem3629225 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term526 A B x' y' f s) = (term527 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629224 A s) (@lem3629212 A B x' y' f s)). Qed.
Lemma lem3629226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3629227 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term528 A B x' y' f s) = (term529 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629226) (@lem3629225 A B x' y' f s)). Qed.
Lemma lem3629228 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term530 A B x' y' f s) = (term531 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629227 A B x' y' f s) (@lem3629047 A B f s)). Qed.
Lemma lem3629229 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) : (term532 A B x' y' f) = (term533 A B x' y' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3629228 A B x' y' f s)). Qed.
Lemma lem3629230 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3629231 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) : (term484 A B x' y' f) = (term534 A B x' y' f).
Proof. exact (MK_COMB (@lem3629230 A) (@lem3629229 A B x' y' f)). Qed.
Lemma lem3629232 {A B : Type'} (x' : type529 A B) (y' : type529 A B) : (term486 A B x' y') = (term535 A B x' y').
Proof. exact (fun_ext (fun f : A -> B => @lem3629231 A B x' y' f)). Qed.
Lemma lem3629233 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3629234 {A B : Type'} (x' : type529 A B) (y' : type529 A B) : (term488 A B x' y') = (term536 A B x' y').
Proof. exact (MK_COMB (@lem3629233 A B) (@lem3629232 A B x' y')). Qed.
Lemma lem3629235 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term536 A B x' y'.
Proof. exact (EQ_MP (@lem3629234 A B x' y') (@lem3628807 A B x' y' h1)). Qed.
Lemma lem3629448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3629449 {B : Type'} : (@INFINITE B) = (@INFINITE B).
Proof. exact (eq_refl (@INFINITE B)). Qed.
Lemma lem3629456 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629457 {A B : Type'} (f : type528 A B) (x : A -> B) : (f x) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem3629456 (A -> B) (type678 A B) f x). Qed.
Lemma lem3629458 {A B : Type'} (f : A -> B) : (@IMAGE A B f) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f).
Proof. exact (@lem3629457 A B (@IMAGE A B) f). Qed.
Lemma lem3629459 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3629460 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s).
Proof. exact (MK_COMB (@lem3629458 A B f) (@lem3629459 A s)). Qed.
Lemma lem3629462 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629463 {A B : Type'} (f : type678 A B) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> B -> Prop) f x).
Proof. exact (@lem3629462 (A -> Prop) (B -> Prop) f x). Qed.
Lemma lem3629464 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f s) = (term494 A B f s).
Proof. exact (@lem3629463 A B (@I ((A -> B) -> (A -> Prop) -> B -> Prop) (@IMAGE A B) f) s). Qed.
Lemma lem3629466 {A B : Type'} (f : A -> B) (s : A -> Prop) : (@IMAGE A B f s) = (term494 A B f s).
Proof. exact (TRANS (@lem3629460 A B f s) (@lem3629464 A B f s)). Qed.
Lemma lem3629467 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term495 A B f s).
Proof. exact (MK_COMB (@lem3629449 B) (@lem3629466 A B f s)). Qed.
Lemma lem3629469 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629470 {B : Type'} (f : type686 B) (x : B -> Prop) : (f x) = (@I ((B -> Prop) -> Prop) f x).
Proof. exact (@lem3629469 (B -> Prop) Prop f x). Qed.
Lemma lem3629471 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term495 A B f s) = (term496 A B f s).
Proof. exact (@lem3629470 B (@INFINITE B) (term494 A B f s)). Qed.
Lemma lem3629472 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term40 A B f s) = (term496 A B f s).
Proof. exact (TRANS (@lem3629467 A B f s) (@lem3629471 A B f s)). Qed.
Lemma lem3629473 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term537 A B f s) = (term538 A B f s).
Proof. exact (MK_COMB (@lem3629448) (@lem3629472 A B f s)). Qed.
Lemma lem3629478 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629479 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3629478 (A -> Prop) Prop f x). Qed.
Lemma lem3629481 {A : Type'} (s : A -> Prop) : (@INFINITE A s) = (@I ((A -> Prop) -> Prop) (@INFINITE A) s).
Proof. exact (@lem3629479 A (@INFINITE A) s). Qed.
Lemma lem3629482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629483 {A : Type'} (s : A -> Prop) : (term33 A s) = (term539 A s).
Proof. exact (MK_COMB (@lem3629482) (@lem3629481 A s)). Qed.
Lemma lem3629484 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term69 A B f s) = (term540 A B f s).
Proof. exact (MK_COMB (@lem3629483 A s) (@lem3629473 A B f s)). Qed.
Lemma lem3629489 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3629490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3629491 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem3629496 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3629496 A B f x). Qed.
Lemma lem3629503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3629504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (@lem3629503 A B f x). Qed.
Lemma lem3629506 {A B : Type'} (f : A -> B) (y : A) : (f y) = (@I (A -> B) f y).
Proof. exact (@lem3629504 A B f y). Qed.
Lemma lem3629507 {A B : Type'} (f : A -> B) (x : A) : (term541 A B f x) = (term542 A B f x).
Proof. exact (MK_COMB (@lem3629491 B) (@lem3629498 A B f x)). Qed.
Lemma lem3629508 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((@I (A -> B) f x) = (@I (A -> B) f y)).
Proof. exact (MK_COMB (@lem3629507 A B f x) (@lem3629506 A B f y)). Qed.
Lemma lem3629509 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term543 A B x f y) = (term544 A B x f y).
Proof. exact (MK_COMB (@lem3629490) (@lem3629508 A B x f y)). Qed.
Lemma lem3629510 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3629511 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term545 A B x f y) = (term546 A B x f y).
Proof. exact (MK_COMB (@lem3629510) (@lem3629509 A B x f y)). Qed.
Lemma lem3629512 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term63 A B f x y) = (term547 A B f x y).
Proof. exact (MK_COMB (@lem3629511 A B x f y) (@lem3629489 A x y)). Qed.
Lemma lem3629513 {A B : Type'} (f : A -> B) (x : A) : (term64 A B f x) = (term548 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3629512 A B f x y)). Qed.
Lemma lem3629514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3629515 {A B : Type'} (f : A -> B) (x : A) : (term65 A B f x) = (term549 A B f x).
Proof. exact (MK_COMB (@lem3629514 A) (@lem3629513 A B f x)). Qed.
Lemma lem3629516 {A B : Type'} (f : A -> B) : (term66 A B f) = (term550 A B f).
Proof. exact (fun_ext (fun x : A => @lem3629515 A B f x)). Qed.
Lemma lem3629517 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3629518 {A B : Type'} (f : A -> B) : (term67 A B f) = (term551 A B f).
Proof. exact (MK_COMB (@lem3629517 A) (@lem3629516 A B f)). Qed.
Lemma lem3629519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629520 {A B : Type'} (f : A -> B) : (term80 A B f) = (term552 A B f).
Proof. exact (MK_COMB (@lem3629519) (@lem3629518 A B f)). Qed.
Lemma lem3629521 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term104 A B f s) = (term553 A B f s).
Proof. exact (MK_COMB (@lem3629520 A B f) (@lem3629484 A B f s)). Qed.
Lemma lem3629522 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term553 A B f s.
Proof. exact (EQ_MP (@lem3629521 A B f s) (@lem3628811 A B f s h1)). Qed.
Lemma lem3629523 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term540 A B f s.
Proof. exact (proj2 (@lem3629522 A B f s h1)). Qed.
Lemma lem3629524 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term551 A B f.
Proof. exact (proj1 (@lem3629522 A B f s h1)). Qed.
Lemma lem3629598 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term496 A B f s) = (term496 A B f s).
Proof. exact (eq_refl (term496 A B f s)). Qed.
Lemma lem3629616 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term527 A B x' y' f s) = (term554 A B x' y' f s).
Proof. exact (@lem19490 (term519 A B x' y' f s) (term524 A s) (term501 A B x' y' f s)). Qed.
Lemma lem3629617 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term555 A B x' y' f s) = (term555 A B x' y' f s).
Proof. exact (eq_refl (term555 A B x' y' f s)). Qed.
Lemma lem3629618 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term556 A B x' y' f s) = (term557 A B x' y' f s).
Proof. exact (@lem19490 (term513 A B x' f s) (term524 A s) (term517 A B x' y' f s)). Qed.
Lemma lem3629625 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term558 A B x' y' f s) = (term559 A B x' y' f s).
Proof. exact (@lem19490 (term513 A B y' f s) (term524 A s) ((term504 A B x' f s) = (term504 A B y' f s))). Qed.
Lemma lem3629628 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term560 A B x' f s) = (term560 A B x' f s).
Proof. exact (eq_refl (term560 A B x' f s)). Qed.
Lemma lem3629629 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term557 A B x' y' f s) = (term561 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629628 A B x' f s) (@lem3629625 A B x' y' f s)). Qed.
Lemma lem3629630 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term556 A B x' y' f s) = (term561 A B x' y' f s).
Proof. exact (TRANS (@lem3629618 A B x' y' f s) (@lem3629629 A B x' y' f s)). Qed.
Lemma lem3629631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629632 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term562 A B x' y' f s) = (term563 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629631) (@lem3629630 A B x' y' f s)). Qed.
Lemma lem3629633 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term554 A B x' y' f s) = (term564 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629632 A B x' y' f s) (@lem3629617 A B x' y' f s)). Qed.
Lemma lem3629635 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term527 A B x' y' f s) = (term564 A B x' y' f s).
Proof. exact (TRANS (@lem3629616 A B x' y' f s) (@lem3629633 A B x' y' f s)). Qed.
Lemma lem3629636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3629637 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term529 A B x' y' f s) = (term565 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629636) (@lem3629635 A B x' y' f s)). Qed.
Lemma lem3629638 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term531 A B x' y' f s) = (term566 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629637 A B x' y' f s) (@lem3629598 A B f s)). Qed.
Lemma lem3629639 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term566 A B x' y' f s) = (term567 A B x' y' f s).
Proof. exact (@lem19699 (term561 A B x' y' f s) (term555 A B x' y' f s) (term496 A B f s)). Qed.
Lemma lem3629640 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term568 A B x' y' f s) = (term568 A B x' y' f s).
Proof. exact (eq_refl (term568 A B x' y' f s)). Qed.
Lemma lem3629641 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term569 A B x' y' f s) = (term570 A B x' y' f s).
Proof. exact (@lem19699 (term571 A B x' f s) (term559 A B x' y' f s) (term496 A B f s)). Qed.
Lemma lem3629648 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term572 A B x' y' f s) = (term573 A B x' y' f s).
Proof. exact (@lem19699 (term571 A B y' f s) (term574 A B x' y' f s) (term496 A B f s)). Qed.
Lemma lem3629651 {A B : Type'} (x' : type529 A B) (f : A -> B) (s : A -> Prop) : (term575 A B x' f s) = (term575 A B x' f s).
Proof. exact (eq_refl (term575 A B x' f s)). Qed.
Lemma lem3629652 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term570 A B x' y' f s) = (term576 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629651 A B x' f s) (@lem3629648 A B x' y' f s)). Qed.
Lemma lem3629653 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term569 A B x' y' f s) = (term576 A B x' y' f s).
Proof. exact (TRANS (@lem3629641 A B x' y' f s) (@lem3629652 A B x' y' f s)). Qed.
Lemma lem3629654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3629655 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term577 A B x' y' f s) = (term578 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629654) (@lem3629653 A B x' y' f s)). Qed.
Lemma lem3629656 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term567 A B x' y' f s) = (term579 A B x' y' f s).
Proof. exact (MK_COMB (@lem3629655 A B x' y' f s) (@lem3629640 A B x' y' f s)). Qed.
Lemma lem3629657 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term566 A B x' y' f s) = (term579 A B x' y' f s).
Proof. exact (TRANS (@lem3629639 A B x' y' f s) (@lem3629656 A B x' y' f s)). Qed.
Lemma lem3629658 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term531 A B x' y' f s) = (term579 A B x' y' f s).
Proof. exact (TRANS (@lem3629638 A B x' y' f s) (@lem3629657 A B x' y' f s)). Qed.
Lemma lem3629659 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) : (term533 A B x' y' f) = (term580 A B x' y' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3629658 A B x' y' f s)). Qed.
Lemma lem3629660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3629661 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) : (term534 A B x' y' f) = (term581 A B x' y' f).
Proof. exact (MK_COMB (@lem3629660 A) (@lem3629659 A B x' y' f)). Qed.
Lemma lem3629662 {A B : Type'} (x' : type529 A B) (y' : type529 A B) : (term535 A B x' y') = (term582 A B x' y').
Proof. exact (fun_ext (fun f : A -> B => @lem3629661 A B x' y' f)). Qed.
Lemma lem3629663 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3629665 {A B : Type'} (x' : type529 A B) (y' : type529 A B) : (term536 A B x' y') = (term583 A B x' y').
Proof. exact (MK_COMB (@lem3629663 A B) (@lem3629662 A B x' y')). Qed.
Lemma lem3629666 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term583 A B x' y'.
Proof. exact (EQ_MP (@lem3629665 A B x' y') (@lem3629235 A B x' y' h1)). Qed.
Lemma lem3629744 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term547 A B f x y) = (term547 A B f x y).
Proof. exact (eq_refl (term547 A B f x y)). Qed.
Lemma lem3629745 {A B : Type'} (f : A -> B) (x : A) : (term548 A B f x) = (term548 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3629744 A B f x y)). Qed.
Lemma lem3629746 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3629747 {A B : Type'} (f : A -> B) (x : A) : (term549 A B f x) = (term549 A B f x).
Proof. exact (MK_COMB (@lem3629746 A) (@lem3629745 A B f x)). Qed.
Lemma lem3629748 {A B : Type'} (f : A -> B) : (term550 A B f) = (term550 A B f).
Proof. exact (fun_ext (fun x : A => @lem3629747 A B f x)). Qed.
Lemma lem3629749 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3629751 {A B : Type'} (f : A -> B) : (term551 A B f) = (term551 A B f).
Proof. exact (MK_COMB (@lem3629749 A) (@lem3629748 A B f)). Qed.
Lemma lem3629752 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term551 A B f.
Proof. exact (EQ_MP (@lem3629751 A B f) (@lem3629524 A B f s h1)). Qed.
Lemma lem3629767 {A B : Type'} (_39532 : A -> B) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term584 A B x' y' _39532.
Proof. exact (@lem3629666 A B x' y' h1 _39532). Qed.
Lemma lem3629768 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) : (term584 A B x' y' _39532) = (term581 A B x' y' _39532).
Proof. exact (eq_refl (term584 A B x' y' _39532)). Qed.
Lemma lem3629769 {A B : Type'} (_39532 : A -> B) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term581 A B x' y' _39532.
Proof. exact (EQ_MP (@lem3629768 A B x' y' _39532) (@lem3629767 A B _39532 x' y' h1)). Qed.
Lemma lem3629770 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term585 A B x' y' _39532 _39533.
Proof. exact (@lem3629769 A B _39532 x' y' h1 _39533). Qed.
Lemma lem3629771 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term585 A B x' y' _39532 _39533) = (term579 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term585 A B x' y' _39532 _39533)). Qed.
Lemma lem3629772 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term579 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3629771 A B x' y' _39532 _39533) (@lem3629770 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629779 {A B : Type'} (_39536 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term586 A B f _39536.
Proof. exact (@lem3629752 A B f s h1 _39536). Qed.
Lemma lem3629780 {A B : Type'} (f : A -> B) (_39536 : A) : (term586 A B f _39536) = (term549 A B f _39536).
Proof. exact (eq_refl (term586 A B f _39536)). Qed.
Lemma lem3629781 {A B : Type'} (_39536 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term549 A B f _39536.
Proof. exact (EQ_MP (@lem3629780 A B f _39536) (@lem3629779 A B _39536 f s h1)). Qed.
Lemma lem3629782 {A B : Type'} (_39536 : A) (_39537 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term587 A B f _39536 _39537.
Proof. exact (@lem3629781 A B _39536 f s h1 _39537). Qed.
Lemma lem3629783 {A B : Type'} (f : A -> B) (_39536 : A) (_39537 : A) : (term587 A B f _39536 _39537) = (term547 A B f _39536 _39537).
Proof. exact (eq_refl (term587 A B f _39536 _39537)). Qed.
Lemma lem3629791 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term568 A B x' y' _39532 _39533.
Proof. exact (proj2 (@lem3629772 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629792 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term576 A B x' y' _39532 _39533.
Proof. exact (proj1 (@lem3629772 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629793 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term573 A B x' y' _39532 _39533.
Proof. exact (proj2 (@lem3629792 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629795 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term588 A B x' y' _39532 _39533.
Proof. exact (proj2 (@lem3629793 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629808 {A B : Type'} (_39536 : A) (_39537 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term547 A B f _39536 _39537.
Proof. exact (EQ_MP (@lem3629783 A B f _39536 _39537) (@lem3629782 A B _39536 _39537 f s h1)). Qed.
Lemma lem3629812 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term538 A B f s.
Proof. exact (proj2 (@lem3629523 A B f s h1)). Qed.
Lemma lem3629871 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term568 A B x' y' _39532 _39533) = (term589 A B x' y' _39532 _39533).
Proof. exact (@lem3626971 (term524 A _39533) (term501 A B x' y' _39532 _39533) (term496 A B _39532 _39533)). Qed.
Lemma lem3629872 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term589 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3629871 A B x' y' _39532 _39533) (@lem3629791 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3629907 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term588 A B x' y' _39532 _39533) = (term590 A B x' y' _39532 _39533).
Proof. exact (@lem3626971 (term524 A _39533) ((term504 A B x' _39532 _39533) = (term504 A B y' _39532 _39533)) (term496 A B _39532 _39533)). Qed.
Lemma lem3629908 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term590 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3629907 A B x' y' _39532 _39533) (@lem3629795 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3630280 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : @I ((A -> Prop) -> Prop) (@INFINITE A) s.
Proof. exact (proj1 (@lem3629523 A B f s h1)). Qed.
Lemma lem3630281 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term591 A s.
Proof. exact (fun h0 : term524 A s => @lem3630280 A B f s h1). Qed.
Lemma lem3630283 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3630284 {A : Type'} (s : A -> Prop) : (term591 A s) = (@I ((A -> Prop) -> Prop) (@INFINITE A) s).
Proof. exact (@lem3630283 (@I ((A -> Prop) -> Prop) (@INFINITE A) s)). Qed.
Lemma lem3630285 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : @I ((A -> Prop) -> Prop) (@INFINITE A) s.
Proof. exact (EQ_MP (@lem3630284 A s) (@lem3630281 A B f s h1)). Qed.
Lemma lem3630287 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : @I ((A -> Prop) -> Prop) (@INFINITE A) s.
Proof. exact (proj1 (@lem3629523 A B f s h1)). Qed.
Lemma lem3630288 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term591 A s.
Proof. exact (fun h0 : term524 A s => @lem3630287 A B f s h1). Qed.
Lemma lem3630290 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3630291 {A : Type'} (s : A -> Prop) : (term591 A s) = (@I ((A -> Prop) -> Prop) (@INFINITE A) s).
Proof. exact (@lem3630290 (@I ((A -> Prop) -> Prop) (@INFINITE A) s)). Qed.
Lemma lem3630292 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : @I ((A -> Prop) -> Prop) (@INFINITE A) s.
Proof. exact (EQ_MP (@lem3630291 A s) (@lem3630288 A B f s h1)). Qed.
Lemma lem3630295 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term538 A B f s) : term538 A B f s.
Proof. exact (h1). Qed.
Lemma lem3630296 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term538 A B f s) : term593 A B f s.
Proof. exact (fun h0 : term496 A B f s => @lem3630295 A B f s h1). Qed.
Lemma lem3630298 (p : Prop) : (term594 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3630299 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term593 A B f s) = (term538 A B f s).
Proof. exact (@lem3630298 (term496 A B f s)). Qed.
Lemma lem3630300 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term538 A B f s) : term538 A B f s.
Proof. exact (EQ_MP (@lem3630299 A B f s) (@lem3630296 A B f s h1)). Qed.
Lemma lem3630306 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3630307 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term589 A B x' y' _39532 _39533) = (term595 A B x' y' _39532 _39533).
Proof. exact (@lem3630306 (term501 A B x' y' _39532 _39533) (term524 A _39533) (term496 A B _39532 _39533)). Qed.
Lemma lem3630323 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3630324 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term596 A B _39532 _39533) = (term597 A B _39532 _39533).
Proof. exact (@lem3630323 (term496 A B _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630330 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term598 A B x' y' _39532 _39533) = (term598 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term598 A B x' y' _39532 _39533)). Qed.
Lemma lem3630331 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term599 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630330 A B x' y' _39532 _39533) (@lem3630324 A B _39532 _39533)). Qed.
Lemma lem3630335 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3630336 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term599 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533).
Proof. exact (@lem3630335 (term496 A B _39532 _39533) (term501 A B x' y' _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630354 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630331 A B x' y' _39532 _39533) (@lem3630336 A B x' y' _39532 _39533)). Qed.
Lemma lem3630355 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term589 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630307 A B x' y' _39532 _39533) (@lem3630354 A B x' y' _39532 _39533)). Qed.
Lemma lem3630356 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3630357 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term601 A B x' y' _39532 _39533) = (term602 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630356) (@lem3630355 A B x' y' _39532 _39533)). Qed.
Lemma lem3630373 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3630374 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term596 A B _39532 _39533) = (term597 A B _39532 _39533).
Proof. exact (@lem3630373 (term496 A B _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630380 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term598 A B x' y' _39532 _39533) = (term598 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term598 A B x' y' _39532 _39533)). Qed.
Lemma lem3630381 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term599 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630380 A B x' y' _39532 _39533) (@lem3630374 A B _39532 _39533)). Qed.
Lemma lem3630385 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3630386 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term599 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533).
Proof. exact (@lem3630385 (term496 A B _39532 _39533) (term501 A B x' y' _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630404 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630381 A B x' y' _39532 _39533) (@lem3630386 A B x' y' _39532 _39533)). Qed.
Lemma lem3630405 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term589 A B x' y' _39532 _39533) = (term595 A B x' y' _39532 _39533)) = ((term600 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533)).
Proof. exact (MK_COMB (@lem3630357 A B x' y' _39532 _39533) (@lem3630404 A B x' y' _39532 _39533)). Qed.
Lemma lem3630407 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3630408 (x : Prop) : (x = x) = True.
Proof. exact (@lem3630407 Prop x). Qed.
Lemma lem3630409 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term600 A B x' y' _39532 _39533) = (term600 A B x' y' _39532 _39533)) = True.
Proof. exact (@lem3630408 (term600 A B x' y' _39532 _39533)). Qed.
Lemma lem3630410 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term589 A B x' y' _39532 _39533) = (term595 A B x' y' _39532 _39533)) = True.
Proof. exact (TRANS (@lem3630405 A B x' y' _39532 _39533) (@lem3630409 A B x' y' _39532 _39533)). Qed.
Lemma lem3630411 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : True = ((term589 A B x' y' _39532 _39533) = (term595 A B x' y' _39532 _39533)).
Proof. exact (SYM (@lem3630410 A B x' y' _39532 _39533)). Qed.
Lemma lem3630412 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term589 A B x' y' _39532 _39533) = (term595 A B x' y' _39532 _39533).
Proof. exact (EQ_MP (@lem3630411 A B x' y' _39532 _39533) (@lem0)). Qed.
Lemma lem3630413 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term595 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3630412 A B x' y' _39532 _39533) (@lem3629872 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3630415 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3630416 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term604 A B x' y' _39532 _39533).
Proof. exact (@lem3630415 (term596 A B _39532 _39533) (term501 A B x' y' _39532 _39533)). Qed.
Lemma lem3630418 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3630419 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term607 A B _39532 _39533) = (term608 A B _39532 _39533).
Proof. exact (@lem3630418 (term524 A _39533) (term496 A B _39532 _39533)). Qed.
Lemma lem3630421 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3630422 {A : Type'} (_39533 : A -> Prop) : (term610 A _39533) = (@I ((A -> Prop) -> Prop) (@INFINITE A) _39533).
Proof. exact (@lem3630421 (@I ((A -> Prop) -> Prop) (@INFINITE A) _39533)). Qed.
Lemma lem3630423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3630424 {A : Type'} (_39533 : A -> Prop) : (term611 A _39533) = (term539 A _39533).
Proof. exact (MK_COMB (@lem3630423) (@lem3630422 A _39533)). Qed.
Lemma lem3630425 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term538 A B _39532 _39533) = (term538 A B _39532 _39533).
Proof. exact (eq_refl (term538 A B _39532 _39533)). Qed.
Lemma lem3630426 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term608 A B _39532 _39533) = (term540 A B _39532 _39533).
Proof. exact (MK_COMB (@lem3630424 A _39533) (@lem3630425 A B _39532 _39533)). Qed.
Lemma lem3630427 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term607 A B _39532 _39533) = (term540 A B _39532 _39533).
Proof. exact (TRANS (@lem3630419 A B _39532 _39533) (@lem3630426 A B _39532 _39533)). Qed.
Lemma lem3630428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3630429 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term612 A B _39532 _39533) = (term613 A B _39532 _39533).
Proof. exact (MK_COMB (@lem3630428) (@lem3630427 A B _39532 _39533)). Qed.
Lemma lem3630430 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term501 A B x' y' _39532 _39533) = (term501 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term501 A B x' y' _39532 _39533)). Qed.
Lemma lem3630431 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term604 A B x' y' _39532 _39533) = (term614 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630429 A B _39532 _39533) (@lem3630430 A B x' y' _39532 _39533)). Qed.
Lemma lem3630432 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term595 A B x' y' _39532 _39533) = (term614 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630416 A B x' y' _39532 _39533) (@lem3630431 A B x' y' _39532 _39533)). Qed.
Lemma lem3630434 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term538 A B f s) (h2 : term104 A B f s) : term540 A B f s.
Proof. exact (conj (@lem3630292 A B f s h2) (@lem3630300 A B f s h1)). Qed.
Lemma lem3630436 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term614 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3630432 A B x' y' _39532 _39533) (@lem3630413 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3630437 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term614 A B x' y' _39532 _39533.
Proof. exact (@lem3630436 A B _39532 _39533 x' y' h1). Qed.
Lemma lem3630438 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term614 A B x' y' f s.
Proof. exact (@lem3630437 A B f s x' y' h1). Qed.
Lemma lem3630441 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term501 A B x' y' f s.
Proof. exact (@lem3630438 A B f s x' y' h1 (@lem3630434 A B f s h2 h3)). Qed.
Lemma lem3630442 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term615 A B x' y' f s.
Proof. exact (fun h0 : (term497 A B x' f s) = (term497 A B y' f s) => @lem3630441 A B x' y' f s h1 h2 h3). Qed.
Lemma lem3630444 (p : Prop) : (term594 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3630445 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term615 A B x' y' f s) = (term501 A B x' y' f s).
Proof. exact (@lem3630444 ((term497 A B x' f s) = (term497 A B y' f s))). Qed.
Lemma lem3630446 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term501 A B x' y' f s.
Proof. exact (EQ_MP (@lem3630445 A B x' y' f s) (@lem3630442 A B x' y' f s h1 h2 h3)). Qed.
Lemma lem3630448 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3630451 {A B : Type'} (_39536 : A) (f : A -> B) (_39537 : A) : (term547 A B f _39536 _39537) = (term616 A B _39536 f _39537).
Proof. exact (@lem3630448 (_39536 = _39537) (term544 A B _39536 f _39537)). Qed.
Lemma lem3630454 {A B : Type'} (_39536 : A) (_39537 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term616 A B _39536 f _39537.
Proof. exact (EQ_MP (@lem3630451 A B _39536 f _39537) (@lem3629808 A B _39536 _39537 f s h1)). Qed.
Lemma lem3630455 {A B : Type'} (_39536 : A) (_39537 : A) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term616 A B _39536 f _39537.
Proof. exact (@lem3630454 A B _39536 _39537 f s h1). Qed.
Lemma lem3630456 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term617 A B x' y' f s.
Proof. exact (@lem3630455 A B (term497 A B x' f s) (term497 A B y' f s) f s h1). Qed.
Lemma lem3630459 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term618 A B x' y' f s.
Proof. exact (@lem3630456 A B x' y' f s h3 (@lem3630446 A B x' y' f s h1 h2 h3)). Qed.
Lemma lem3630460 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term619 A B x' y' f s.
Proof. exact (fun h0 : (term504 A B x' f s) = (term504 A B y' f s) => @lem3630459 A B x' y' f s h1 h2 h3). Qed.
Lemma lem3630462 (p : Prop) : (term594 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3630463 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) : (term619 A B x' y' f s) = (term618 A B x' y' f s).
Proof. exact (@lem3630462 ((term504 A B x' f s) = (term504 A B y' f s))). Qed.
Lemma lem3630464 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term618 A B x' y' f s.
Proof. exact (EQ_MP (@lem3630463 A B x' y' f s) (@lem3630460 A B x' y' f s h1 h2 h3)). Qed.
Lemma lem3630470 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3630471 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term590 A B x' y' _39532 _39533) = (term620 A B x' y' _39532 _39533).
Proof. exact (@lem3630470 ((term504 A B x' _39532 _39533) = (term504 A B y' _39532 _39533)) (term524 A _39533) (term496 A B _39532 _39533)). Qed.
Lemma lem3630487 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3630488 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term596 A B _39532 _39533) = (term597 A B _39532 _39533).
Proof. exact (@lem3630487 (term496 A B _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630494 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term621 A B x' y' _39532 _39533) = (term621 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term621 A B x' y' _39532 _39533)). Qed.
Lemma lem3630495 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term620 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630494 A B x' y' _39532 _39533) (@lem3630488 A B _39532 _39533)). Qed.
Lemma lem3630506 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term590 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630471 A B x' y' _39532 _39533) (@lem3630495 A B x' y' _39532 _39533)). Qed.
Lemma lem3630507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3630508 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term623 A B x' y' _39532 _39533) = (term624 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630507) (@lem3630506 A B x' y' _39532 _39533)). Qed.
Lemma lem3630522 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3630523 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term574 A B x' y' _39532 _39533) = (term625 A B x' y' _39532 _39533).
Proof. exact (@lem3630522 ((term504 A B x' _39532 _39533) = (term504 A B y' _39532 _39533)) (term524 A _39533)). Qed.
Lemma lem3630531 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term626 A B _39532 _39533) = (term626 A B _39532 _39533).
Proof. exact (eq_refl (term626 A B _39532 _39533)). Qed.
Lemma lem3630532 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term627 A B x' y' _39532 _39533) = (term628 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630531 A B _39532 _39533) (@lem3630523 A B x' y' _39532 _39533)). Qed.
Lemma lem3630536 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3630537 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term628 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533).
Proof. exact (@lem3630536 ((term504 A B x' _39532 _39533) = (term504 A B y' _39532 _39533)) (term496 A B _39532 _39533) (term524 A _39533)). Qed.
Lemma lem3630555 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term627 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630532 A B x' y' _39532 _39533) (@lem3630537 A B x' y' _39532 _39533)). Qed.
Lemma lem3630556 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term590 A B x' y' _39532 _39533) = (term627 A B x' y' _39532 _39533)) = ((term622 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533)).
Proof. exact (MK_COMB (@lem3630508 A B x' y' _39532 _39533) (@lem3630555 A B x' y' _39532 _39533)). Qed.
Lemma lem3630558 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3630559 (x : Prop) : (x = x) = True.
Proof. exact (@lem3630558 Prop x). Qed.
Lemma lem3630560 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term622 A B x' y' _39532 _39533) = (term622 A B x' y' _39532 _39533)) = True.
Proof. exact (@lem3630559 (term622 A B x' y' _39532 _39533)). Qed.
Lemma lem3630561 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : ((term590 A B x' y' _39532 _39533) = (term627 A B x' y' _39532 _39533)) = True.
Proof. exact (TRANS (@lem3630556 A B x' y' _39532 _39533) (@lem3630560 A B x' y' _39532 _39533)). Qed.
Lemma lem3630562 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : True = ((term590 A B x' y' _39532 _39533) = (term627 A B x' y' _39532 _39533)).
Proof. exact (SYM (@lem3630561 A B x' y' _39532 _39533)). Qed.
Lemma lem3630563 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term590 A B x' y' _39532 _39533) = (term627 A B x' y' _39532 _39533).
Proof. exact (EQ_MP (@lem3630562 A B x' y' _39532 _39533) (@lem0)). Qed.
Lemma lem3630564 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term627 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3630563 A B x' y' _39532 _39533) (@lem3629908 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3630566 (b : Prop) (a : Prop) : (a \/ b) = (term603 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3630567 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term627 A B x' y' _39532 _39533) = (term629 A B x' y' _39532 _39533).
Proof. exact (@lem3630566 (term574 A B x' y' _39532 _39533) (term496 A B _39532 _39533)). Qed.
Lemma lem3630569 (a : Prop) (b : Prop) : (term605 a b) = (term606 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3630570 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term630 A B x' y' _39532 _39533) = (term631 A B x' y' _39532 _39533).
Proof. exact (@lem3630569 (term524 A _39533) ((term504 A B x' _39532 _39533) = (term504 A B y' _39532 _39533))). Qed.
Lemma lem3630572 (a : Prop) : (term609 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3630573 {A : Type'} (_39533 : A -> Prop) : (term610 A _39533) = (@I ((A -> Prop) -> Prop) (@INFINITE A) _39533).
Proof. exact (@lem3630572 (@I ((A -> Prop) -> Prop) (@INFINITE A) _39533)). Qed.
Lemma lem3630574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3630575 {A : Type'} (_39533 : A -> Prop) : (term611 A _39533) = (term539 A _39533).
Proof. exact (MK_COMB (@lem3630574) (@lem3630573 A _39533)). Qed.
Lemma lem3630576 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term618 A B x' y' _39532 _39533) = (term618 A B x' y' _39532 _39533).
Proof. exact (eq_refl (term618 A B x' y' _39532 _39533)). Qed.
Lemma lem3630577 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term631 A B x' y' _39532 _39533) = (term632 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630575 A _39533) (@lem3630576 A B x' y' _39532 _39533)). Qed.
Lemma lem3630578 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term630 A B x' y' _39532 _39533) = (term632 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630570 A B x' y' _39532 _39533) (@lem3630577 A B x' y' _39532 _39533)). Qed.
Lemma lem3630579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3630580 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term633 A B x' y' _39532 _39533) = (term634 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630579) (@lem3630578 A B x' y' _39532 _39533)). Qed.
Lemma lem3630581 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) : (term496 A B _39532 _39533) = (term496 A B _39532 _39533).
Proof. exact (eq_refl (term496 A B _39532 _39533)). Qed.
Lemma lem3630582 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term629 A B x' y' _39532 _39533) = (term635 A B x' y' _39532 _39533).
Proof. exact (MK_COMB (@lem3630580 A B x' y' _39532 _39533) (@lem3630581 A B _39532 _39533)). Qed.
Lemma lem3630583 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (_39532 : A -> B) (_39533 : A -> Prop) : (term627 A B x' y' _39532 _39533) = (term635 A B x' y' _39532 _39533).
Proof. exact (TRANS (@lem3630567 A B x' y' _39532 _39533) (@lem3630582 A B x' y' _39532 _39533)). Qed.
Lemma lem3630585 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term632 A B x' y' f s.
Proof. exact (conj (@lem3630285 A B f s h3) (@lem3630464 A B x' y' f s h1 h2 h3)). Qed.
Lemma lem3630587 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term635 A B x' y' _39532 _39533.
Proof. exact (EQ_MP (@lem3630583 A B x' y' _39532 _39533) (@lem3630564 A B _39532 _39533 x' y' h1)). Qed.
Lemma lem3630588 {A B : Type'} (_39532 : A -> B) (_39533 : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term635 A B x' y' _39532 _39533.
Proof. exact (@lem3630587 A B _39532 _39533 x' y' h1). Qed.
Lemma lem3630589 {A B : Type'} (f : A -> B) (s : A -> Prop) (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') : term635 A B x' y' f s.
Proof. exact (@lem3630588 A B f s x' y' h1). Qed.
Lemma lem3630592 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term538 A B f s) (h3 : term104 A B f s) : term496 A B f s.
Proof. exact (@lem3630589 A B f s x' y' h1 (@lem3630585 A B x' y' f s h1 h2 h3)). Qed.
Lemma lem3630593 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term104 A B f s) : term636 A B f s.
Proof. exact (fun h0 : term538 A B f s => @lem3630592 A B x' y' f s h1 h0 h2). Qed.
Lemma lem3630595 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3630596 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term636 A B f s) = (term496 A B f s).
Proof. exact (@lem3630595 (term496 A B f s)). Qed.
Lemma lem3630597 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term104 A B f s) : term496 A B f s.
Proof. exact (EQ_MP (@lem3630596 A B f s) (@lem3630593 A B x' y' f s h1 h2)). Qed.
Lemma lem3630600 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3630602 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term538 A B f s) = (term637 A B f s).
Proof. exact (@lem3630600 (term496 A B f s)). Qed.
Lemma lem3630605 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term104 A B f s) : term637 A B f s.
Proof. exact (EQ_MP (@lem3630602 A B f s) (@lem3629812 A B f s h1)). Qed.
Lemma lem3630608 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term104 A B f s) : False.
Proof. exact (@lem3630605 A B f s h2 (@lem3630597 A B x' y' f s h1 h2)). Qed.
Lemma lem3630609 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term104 A B f s) : term638.
Proof. exact (fun h0 : ~ False => @lem3630608 A B x' y' f s h1 h2). Qed.
Lemma lem3630611 (p : Prop) : (term592 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3630612 : term638 = False.
Proof. exact (@lem3630611 False). Qed.
Lemma lem3630613 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (s : A -> Prop) (h1 : term488 A B x' y') (h2 : term104 A B f s) : False.
Proof. exact (EQ_MP (@lem3630612) (@lem3630609 A B x' y' f s h1 h2)). Qed.
Lemma lem3630614 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (f : A -> B) (h1 : term488 A B x' y') (h2 : term107 A B f) : False.
Proof. exact (ex_elim (@lem3628810 A B f h2) (fun s : A -> Prop => fun h0 : term106 A B f s => @lem3630613 A B x' y' f s h1 h0)). Qed.
Lemma lem3630615 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (h1 : term488 A B x' y') (h2 : term10 A B) : False.
Proof. exact (ex_elim (@lem3627609 A B h2) (fun f : A -> B => fun h0 : term108 A B f => @lem3630614 A B x' y' f h1 h0)). Qed.
Lemma lem3630616 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (x'' : type485 A) (h1 : term488 A B x' y') (h2 : term305 A x'') (h3 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628808 A x'' h2) (fun y'' : type485 A => fun h0 : term304 A x'' y'' => @lem3630615 A B x' y' h1 h3)). Qed.
Lemma lem3630617 {A B : Type'} (x' : type529 A B) (y' : type529 A B) (h1 : term12 A) (h2 : term488 A B x' y') (h3 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628007 A h1) (fun x'' : type485 A => fun h0 : term306 A x'' => @lem3630616 A B x' y' x'' h2 h0 h3)). Qed.
Lemma lem3630618 {A B : Type'} (x' : type529 A B) (h1 : term12 A) (h2 : term491 A B x') (h3 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628806 A B x' h2) (fun y' : type529 A B => fun h0 : term490 A B x' y' => @lem3630617 A B x' y' h1 h0 h3)). Qed.
Lemma lem3630619 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628405 A B h2) (fun x' : type529 A B => fun h0 : term492 A B x' => @lem3630618 A B x' h1 h0 h3)). Qed.
Lemma lem3630620 {A B : Type'} (x : type485 B) (h1 : term12 A) (h2 : term11 A B) (h3 : term305 B x) (h4 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628804 B x h3) (fun y : type485 B => fun h0 : term304 B x y => @lem3630619 A B h1 h2 h4)). Qed.
Lemma lem3630621 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term12 B) (h4 : term10 A B) : False.
Proof. exact (ex_elim (@lem3628803 B h3) (fun x : type485 B => fun h0 : term306 B x => @lem3630620 A B x h1 h2 h0 h4)). Qed.
Lemma lem3630622 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term10 A B) : term17 B.
Proof. exact (fun h0 : term12 B => @lem3630621 A B h1 h2 h0 h3). Qed.
Lemma lem3630623 {B : Type'} : (term17 B) = (term18 B).
Proof. exact (@lem69 (term12 B)). Qed.
Lemma lem3630624 {A B : Type'} (h1 : term12 A) (h2 : term11 A B) (h3 : term10 A B) : term18 B.
Proof. exact (EQ_MP (@lem3630623 B) (@lem3630622 A B h1 h2 h3)). Qed.
Lemma lem3630625 {A B : Type'} (h1 : term12 A) (h2 : term10 A B) : term21 A B.
Proof. exact (fun h0 : term11 A B => @lem3630624 A B h1 h0 h2). Qed.
Lemma lem3630626 {A B : Type'} (h1 : term10 A B) : term24 A B.
Proof. exact (fun h0 : term12 A => @lem3630625 A B h0 h1). Qed.
Lemma lem3630627 {A B : Type'} : term26 A B.
Proof. exact (fun h0 : term10 A B => @lem3630626 A B h0). Qed.
Lemma lem3630628 {A B : Type'} : term13 A B.
Proof. exact (EQ_MP (@lem3627405 A B) (@lem3630627 A B)). Qed.
Lemma lem3630630 {A B : Type'} : term13 A B.
Proof. exact (@lem3627001 A B (@lem3630628 A B)). Qed.
Lemma lem3630631 {A B : Type'} (h1 : term10 A B) : term23 A B.
Proof. exact (@lem3630630 A B (@lem3626976 A B h1)). Qed.
Lemma lem3630632 {A B : Type'} (h1 : term10 A B) : term20 A B.
Proof. exact (@lem3630631 A B h1 (@lem3626980 A)). Qed.
Lemma lem3630633 {A B : Type'} (h1 : term10 A B) : term17 B.
Proof. exact (@lem3630632 A B h1 (@lem3626977 A B)). Qed.
Lemma lem3630634 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem3630633 A B h1 (@lem3626978 B)). Qed.
Lemma lem3630635 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem3630634 A B h1) (fun h2 : False => @lem3626976 A B h1)). Qed.
Lemma lem3630636 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem3630635 A B h1) (@lem3626976 A B h1)). Qed.
Lemma lem3630637 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem3630636 A B h0). Qed.
Lemma lem3630638 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem3626975 A B) (@lem3630637 A B)). Qed.
