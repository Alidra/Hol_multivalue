Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_CHAIN_UNIONS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import pairwise_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem4821879 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4821880 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4821881 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4821880 t1) (@lem4821879 t1)). Qed.
Lemma lem4821882 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4821881 t1 t2). Qed.
Lemma lem4821883 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4821884 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4821883 t1 t2) (@lem4821882 t1 t2)). Qed.
Lemma lem4821885 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4821884 t1 t2 t3). Qed.
Lemma lem4821886 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4821887 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4821886 t1 t2 t3) (@lem4821885 t1 t2 t3)). Qed.
Lemma lem4821888 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4821887 t1 t2 t3)). Qed.
Lemma lem4821889 {_110510 : Type'} (s : _110510 -> Prop) : term7 _110510 s.
Proof. exact (@lem4794393 _110510 s). Qed.
Lemma lem4821890 {_110510 : Type'} (s : _110510 -> Prop) : (term7 _110510 s) = (term8 _110510 s).
Proof. exact (eq_refl (term7 _110510 s)). Qed.
Lemma lem4821891 {_110510 : Type'} (s : _110510 -> Prop) : term8 _110510 s.
Proof. exact (EQ_MP (@lem4821890 _110510 s) (@lem4821889 _110510 s)). Qed.
Lemma lem4821892 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : term9 _110510 s r.
Proof. exact (@lem4821891 _110510 s r). Qed.
Lemma lem4821893 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (term9 _110510 s r) = ((@pairwise _110510 r s) = (term10 _110510 s r)).
Proof. exact (eq_refl (term9 _110510 s r)). Qed.
Lemma lem4821914 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4821893 _110510 s r) (@lem4821892 _110510 s r)). Qed.
Lemma lem4821915 {A : Type'} (s : A -> Prop) (r : type1402 A) : (@pairwise A r s) = (term10 A s r).
Proof. exact (@lem4821914 A s r). Qed.
Lemma lem4821916 {A : Type'} (s : A -> Prop) (R : type1402 A) : (@pairwise A R s) = (term10 A s R).
Proof. exact (@lem4821915 A s R). Qed.
Lemma lem4821933 {A : Type'} (s : A -> Prop) (c : type686 A) : (term11 A s c) = (term11 A s c).
Proof. exact (eq_refl (term11 A s c)). Qed.
Lemma lem4821934 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term12 A c R s) = (term13 A c s R).
Proof. exact (MK_COMB (@lem4821933 A s c) (@lem4821916 A s R)). Qed.
Lemma lem4821937 {A : Type'} (c : type686 A) (R : type1402 A) : (term14 A c R) = (term15 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4821934 A c s R)). Qed.
Lemma lem4821938 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4821939 {A : Type'} (c : type686 A) (R : type1402 A) : (term16 A c R) = (term17 A c R).
Proof. exact (MK_COMB (@lem4821938 A) (@lem4821937 A c R)). Qed.
Lemma lem4821944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4821945 {A : Type'} (c : type686 A) (R : type1402 A) : (term18 A c R) = (term19 A c R).
Proof. exact (MK_COMB (@lem4821944) (@lem4821939 A c R)). Qed.
Lemma lem4821960 {A : Type'} (c : type686 A) : (term20 A c) = (term20 A c).
Proof. exact (eq_refl (term20 A c)). Qed.
Lemma lem4821961 {A : Type'} (R : type1402 A) (c : type686 A) : (term21 A R c) = (term22 A R c).
Proof. exact (MK_COMB (@lem4821945 A c R) (@lem4821960 A c)). Qed.
Lemma lem4821964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4821965 {A : Type'} (R : type1402 A) (c : type686 A) : (term23 A R c) = (term24 A R c).
Proof. exact (MK_COMB (@lem4821964) (@lem4821961 A R c)). Qed.
Lemma lem4821967 {_110510 : Type'} (s : _110510 -> Prop) (r : type1402 _110510) : (@pairwise _110510 r s) = (term10 _110510 s r).
Proof. exact (EQ_MP (@lem4821893 _110510 s r) (@lem4821892 _110510 s r)). Qed.
Lemma lem4821968 {A : Type'} (s : A -> Prop) (r : type1402 A) : (@pairwise A r s) = (term10 A s r).
Proof. exact (@lem4821967 A s r). Qed.
Lemma lem4821969 {A : Type'} (c : type686 A) (R : type1402 A) : (term25 A R c) = (term26 A c R).
Proof. exact (@lem4821968 A (@UNIONS A c) R). Qed.
Lemma lem4821986 {A : Type'} (c : type686 A) (R : type1402 A) : (term27 A R c) = (term28 A c R).
Proof. exact (MK_COMB (@lem4821965 A R c) (@lem4821969 A c R)). Qed.
Lemma lem4821989 {A : Type'} (R : type1402 A) : (term29 A R) = (term30 A R).
Proof. exact (fun_ext (fun c : type686 A => @lem4821986 A c R)). Qed.
Lemma lem4821990 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4821991 {A : Type'} (R : type1402 A) : (term31 A R) = (term32 A R).
Proof. exact (MK_COMB (@lem4821990 A) (@lem4821989 A R)). Qed.
Lemma lem4821996 {A : Type'} : (term33 A) = (term34 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem4821991 A R)). Qed.
Lemma lem4821997 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4821998 {A : Type'} : (term35 A) = (term36 A).
Proof. exact (MK_COMB (@lem4821997 A) (@lem4821996 A)). Qed.
Lemma lem4822003 {A : Type'} : (term36 A) = (term35 A).
Proof. exact (SYM (@lem4821998 A)). Qed.
Lemma lem4822055 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term37 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4822056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term37 A s t).
Proof. exact (@lem4822055 A s t). Qed.
Lemma lem4822063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem4822063) (@lem4822056 A s t)). Qed.
Lemma lem4822066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term37 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4822067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term37 A s t).
Proof. exact (@lem4822066 A s t). Qed.
Lemma lem4822068 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term37 A t s).
Proof. exact (@lem4822067 A t s). Qed.
Lemma lem4822075 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term40 A t s) = (term41 A t s).
Proof. exact (MK_COMB (@lem4822064 A s t) (@lem4822068 A t s)). Qed.
Lemma lem4822078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (c : type686 A) : (term42 A s t c) = (term42 A s t c).
Proof. exact (eq_refl (term42 A s t c)). Qed.
Lemma lem4822079 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term43 A c t s) = (term44 A c t s).
Proof. exact (MK_COMB (@lem4822078 A s t c) (@lem4822075 A t s)). Qed.
Lemma lem4822082 {A : Type'} (c : type686 A) (s : A -> Prop) : (term45 A c s) = (term46 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822079 A c t s)). Qed.
Lemma lem4822083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822084 {A : Type'} (c : type686 A) (s : A -> Prop) : (term47 A c s) = (term48 A c s).
Proof. exact (MK_COMB (@lem4822083 A) (@lem4822082 A c s)). Qed.
Lemma lem4822089 {A : Type'} (c : type686 A) : (term49 A c) = (term50 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822084 A c s)). Qed.
Lemma lem4822090 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822091 {A : Type'} (c : type686 A) : (term20 A c) = (term51 A c).
Proof. exact (MK_COMB (@lem4822090 A) (@lem4822089 A c)). Qed.
Lemma lem4822096 {A : Type'} (c : type686 A) (R : type1402 A) : (term19 A c R) = (term19 A c R).
Proof. exact (eq_refl (term19 A c R)). Qed.
Lemma lem4822097 {A : Type'} (R : type1402 A) (c : type686 A) : (term22 A R c) = (term52 A R c).
Proof. exact (MK_COMB (@lem4822096 A c R) (@lem4822091 A c)). Qed.
Lemma lem4822100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822101 {A : Type'} (R : type1402 A) (c : type686 A) : (term24 A R c) = (term53 A R c).
Proof. exact (MK_COMB (@lem4822100) (@lem4822097 A R c)). Qed.
Lemma lem4822120 {A : Type'} (c : type686 A) (R : type1402 A) : (term26 A c R) = (term26 A c R).
Proof. exact (eq_refl (term26 A c R)). Qed.
Lemma lem4822121 {A : Type'} (c : type686 A) (R : type1402 A) : (term28 A c R) = (term54 A c R).
Proof. exact (MK_COMB (@lem4822101 A R c) (@lem4822120 A c R)). Qed.
Lemma lem4822124 {A : Type'} (R : type1402 A) : (term30 A R) = (term55 A R).
Proof. exact (fun_ext (fun c : type686 A => @lem4822121 A c R)). Qed.
Lemma lem4822125 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4822126 {A : Type'} (R : type1402 A) : (term32 A R) = (term56 A R).
Proof. exact (MK_COMB (@lem4822125 A) (@lem4822124 A R)). Qed.
Lemma lem4822131 {A : Type'} : (term34 A) = (term57 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem4822126 A R)). Qed.
Lemma lem4822132 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4822133 {A : Type'} : (term36 A) = (term58 A).
Proof. exact (MK_COMB (@lem4822132 A) (@lem4822131 A)). Qed.
Lemma lem4822138 {A : Type'} : (term58 A) = (term36 A).
Proof. exact (SYM (@lem4822133 A)). Qed.
Lemma lem4822158 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822159 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4822158 (A -> Prop) P x). Qed.
Lemma lem4822160 {A : Type'} (c : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s c) = (c s).
Proof. exact (@lem4822159 A c s). Qed.
Lemma lem4822161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822162 {A : Type'} (c : type686 A) (s : A -> Prop) : (term11 A s c) = (term59 A c s).
Proof. exact (MK_COMB (@lem4822161) (@lem4822160 A c s)). Qed.
Lemma lem4822176 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822177 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822176 A P x). Qed.
Lemma lem4822178 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4822177 A s x). Qed.
Lemma lem4822179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822180 {A : Type'} (s : A -> Prop) (x : A) : (term60 A x s) = (term61 A s x).
Proof. exact (MK_COMB (@lem4822179) (@lem4822178 A s x)). Qed.
Lemma lem4822184 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822185 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822184 A P x). Qed.
Lemma lem4822186 {A : Type'} (s : A -> Prop) (y : A) : (@IN A y s) = (s y).
Proof. exact (@lem4822185 A s y). Qed.
Lemma lem4822187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822188 {A : Type'} (s : A -> Prop) (y : A) : (term60 A y s) = (term61 A s y).
Proof. exact (MK_COMB (@lem4822187) (@lem4822186 A s y)). Qed.
Lemma lem4822191 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4822192 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term63 A s x y) = (term64 A s x y).
Proof. exact (MK_COMB (@lem4822188 A s y) (@lem4822191 A x y)). Qed.
Lemma lem4822195 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term65 A s x y) = (term66 A s x y).
Proof. exact (MK_COMB (@lem4822180 A s x) (@lem4822192 A s x y)). Qed.
Lemma lem4822198 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822199 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term67 A s x y) = (term68 A s x y).
Proof. exact (MK_COMB (@lem4822198) (@lem4822195 A s x y)). Qed.
Lemma lem4822200 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4822201 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term69 A s R x y) = (term70 A s R x y).
Proof. exact (MK_COMB (@lem4822199 A s x y) (@lem4822200 A R x y)). Qed.
Lemma lem4822204 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term71 A s R x) = (term72 A s R x).
Proof. exact (fun_ext (fun y : A => @lem4822201 A s R x y)). Qed.
Lemma lem4822205 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822206 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term73 A s R x) = (term74 A s R x).
Proof. exact (MK_COMB (@lem4822205 A) (@lem4822204 A s R x)). Qed.
Lemma lem4822211 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term75 A s R) = (term76 A s R).
Proof. exact (fun_ext (fun x : A => @lem4822206 A s R x)). Qed.
Lemma lem4822212 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822213 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term10 A s R) = (term77 A s R).
Proof. exact (MK_COMB (@lem4822212 A) (@lem4822211 A s R)). Qed.
Lemma lem4822218 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term13 A c s R) = (term78 A c s R).
Proof. exact (MK_COMB (@lem4822162 A c s) (@lem4822213 A s R)). Qed.
Lemma lem4822221 {A : Type'} (c : type686 A) (R : type1402 A) : (term15 A c R) = (term79 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822218 A c s R)). Qed.
Lemma lem4822222 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822223 {A : Type'} (c : type686 A) (R : type1402 A) : (term17 A c R) = (term80 A c R).
Proof. exact (MK_COMB (@lem4822222 A) (@lem4822221 A c R)). Qed.
Lemma lem4822228 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822229 {A : Type'} (c : type686 A) (R : type1402 A) : (term19 A c R) = (term81 A c R).
Proof. exact (MK_COMB (@lem4822228) (@lem4822223 A c R)). Qed.
Lemma lem4822243 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822244 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4822243 (A -> Prop) P x). Qed.
Lemma lem4822245 {A : Type'} (c : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s c) = (c s).
Proof. exact (@lem4822244 A c s). Qed.
Lemma lem4822246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822247 {A : Type'} (c : type686 A) (s : A -> Prop) : (term82 A s c) = (term83 A c s).
Proof. exact (MK_COMB (@lem4822246) (@lem4822245 A c s)). Qed.
Lemma lem4822249 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822250 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4822249 (A -> Prop) P x). Qed.
Lemma lem4822251 {A : Type'} (c : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t c) = (c t).
Proof. exact (@lem4822250 A c t). Qed.
Lemma lem4822252 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term84 A s t c) = (term85 A s c t).
Proof. exact (MK_COMB (@lem4822247 A c s) (@lem4822251 A c t)). Qed.
Lemma lem4822255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822256 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term42 A s t c) = (term86 A s c t).
Proof. exact (MK_COMB (@lem4822255) (@lem4822252 A s c t)). Qed.
Lemma lem4822266 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822266 A P x). Qed.
Lemma lem4822268 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4822267 A s x). Qed.
Lemma lem4822269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822270 {A : Type'} (s : A -> Prop) (x : A) : (term87 A x s) = (term88 A s x).
Proof. exact (MK_COMB (@lem4822269) (@lem4822268 A s x)). Qed.
Lemma lem4822272 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822273 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822272 A P x). Qed.
Lemma lem4822274 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4822273 A t x). Qed.
Lemma lem4822275 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term89 A s x t) = (term90 A s t x).
Proof. exact (MK_COMB (@lem4822270 A s x) (@lem4822274 A t x)). Qed.
Lemma lem4822278 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term92 A s t).
Proof. exact (fun_ext (fun x : A => @lem4822275 A s t x)). Qed.
Lemma lem4822279 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822280 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term37 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem4822279 A) (@lem4822278 A s t)). Qed.
Lemma lem4822285 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822286 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term94 A s t).
Proof. exact (MK_COMB (@lem4822285) (@lem4822280 A s t)). Qed.
Lemma lem4822294 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822295 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822294 A P x). Qed.
Lemma lem4822296 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4822295 A t x). Qed.
Lemma lem4822297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822298 {A : Type'} (t : A -> Prop) (x : A) : (term87 A x t) = (term88 A t x).
Proof. exact (MK_COMB (@lem4822297) (@lem4822296 A t x)). Qed.
Lemma lem4822300 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822301 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822300 A P x). Qed.
Lemma lem4822302 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4822301 A s x). Qed.
Lemma lem4822303 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term89 A t x s) = (term90 A t s x).
Proof. exact (MK_COMB (@lem4822298 A t x) (@lem4822302 A s x)). Qed.
Lemma lem4822306 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term91 A t s) = (term92 A t s).
Proof. exact (fun_ext (fun x : A => @lem4822303 A t s x)). Qed.
Lemma lem4822307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822308 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term37 A t s) = (term93 A t s).
Proof. exact (MK_COMB (@lem4822307 A) (@lem4822306 A t s)). Qed.
Lemma lem4822313 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term41 A t s) = (term95 A t s).
Proof. exact (MK_COMB (@lem4822286 A s t) (@lem4822308 A t s)). Qed.
Lemma lem4822316 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term44 A c t s) = (term96 A c t s).
Proof. exact (MK_COMB (@lem4822256 A s c t) (@lem4822313 A t s)). Qed.
Lemma lem4822319 {A : Type'} (c : type686 A) (s : A -> Prop) : (term46 A c s) = (term97 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822316 A c t s)). Qed.
Lemma lem4822320 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822321 {A : Type'} (c : type686 A) (s : A -> Prop) : (term48 A c s) = (term98 A c s).
Proof. exact (MK_COMB (@lem4822320 A) (@lem4822319 A c s)). Qed.
Lemma lem4822326 {A : Type'} (c : type686 A) : (term50 A c) = (term99 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822321 A c s)). Qed.
Lemma lem4822327 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822328 {A : Type'} (c : type686 A) : (term51 A c) = (term100 A c).
Proof. exact (MK_COMB (@lem4822327 A) (@lem4822326 A c)). Qed.
Lemma lem4822333 {A : Type'} (R : type1402 A) (c : type686 A) : (term52 A R c) = (term101 A R c).
Proof. exact (MK_COMB (@lem4822229 A c R) (@lem4822328 A c)). Qed.
Lemma lem4822336 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822337 {A : Type'} (R : type1402 A) (c : type686 A) : (term53 A R c) = (term102 A R c).
Proof. exact (MK_COMB (@lem4822336) (@lem4822333 A R c)). Qed.
Lemma lem4822351 {A : Type'} (s : type686 A) (x : A) : (term103 A x s) = (term104 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4822352 {A : Type'} (s : type686 A) (x : A) : (term103 A x s) = (term104 A s x).
Proof. exact (@lem4822351 A s x). Qed.
Lemma lem4822353 {A : Type'} (c : type686 A) (x : A) : (term103 A x c) = (term104 A c x).
Proof. exact (@lem4822352 A c x). Qed.
Lemma lem4822361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822362 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4822361 (A -> Prop) P x). Qed.
Lemma lem4822363 {A : Type'} (c : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t c) = (c t).
Proof. exact (@lem4822362 A c t). Qed.
Lemma lem4822364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822365 {A : Type'} (c : type686 A) (t : A -> Prop) : (term82 A t c) = (term83 A c t).
Proof. exact (MK_COMB (@lem4822364) (@lem4822363 A c t)). Qed.
Lemma lem4822367 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822368 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822367 A P x). Qed.
Lemma lem4822369 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4822368 A t x). Qed.
Lemma lem4822370 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term105 A c x t) = (term106 A c t x).
Proof. exact (MK_COMB (@lem4822365 A c t) (@lem4822369 A t x)). Qed.
Lemma lem4822373 {A : Type'} (c : type686 A) (x : A) : (term107 A c x) = (term108 A c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822370 A c t x)). Qed.
Lemma lem4822374 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4822375 {A : Type'} (c : type686 A) (x : A) : (term104 A c x) = (term109 A c x).
Proof. exact (MK_COMB (@lem4822374 A) (@lem4822373 A c x)). Qed.
Lemma lem4822380 {A : Type'} (c : type686 A) (x : A) : (term103 A x c) = (term109 A c x).
Proof. exact (TRANS (@lem4822353 A c x) (@lem4822375 A c x)). Qed.
Lemma lem4822381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822382 {A : Type'} (c : type686 A) (x : A) : (term110 A x c) = (term111 A c x).
Proof. exact (MK_COMB (@lem4822381) (@lem4822380 A c x)). Qed.
Lemma lem4822386 {A : Type'} (s : type686 A) (x : A) : (term103 A x s) = (term104 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4822387 {A : Type'} (s : type686 A) (x : A) : (term103 A x s) = (term104 A s x).
Proof. exact (@lem4822386 A s x). Qed.
Lemma lem4822388 {A : Type'} (c : type686 A) (y : A) : (term103 A y c) = (term104 A c y).
Proof. exact (@lem4822387 A c y). Qed.
Lemma lem4822396 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822397 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4822396 (A -> Prop) P x). Qed.
Lemma lem4822398 {A : Type'} (c : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t c) = (c t).
Proof. exact (@lem4822397 A c t). Qed.
Lemma lem4822399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822400 {A : Type'} (c : type686 A) (t : A -> Prop) : (term82 A t c) = (term83 A c t).
Proof. exact (MK_COMB (@lem4822399) (@lem4822398 A c t)). Qed.
Lemma lem4822402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4822403 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4822402 A P x). Qed.
Lemma lem4822404 {A : Type'} (t : A -> Prop) (y : A) : (@IN A y t) = (t y).
Proof. exact (@lem4822403 A t y). Qed.
Lemma lem4822405 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term105 A c y t) = (term106 A c t y).
Proof. exact (MK_COMB (@lem4822400 A c t) (@lem4822404 A t y)). Qed.
Lemma lem4822408 {A : Type'} (c : type686 A) (y : A) : (term107 A c y) = (term108 A c y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822405 A c t y)). Qed.
Lemma lem4822409 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4822410 {A : Type'} (c : type686 A) (y : A) : (term104 A c y) = (term109 A c y).
Proof. exact (MK_COMB (@lem4822409 A) (@lem4822408 A c y)). Qed.
Lemma lem4822415 {A : Type'} (c : type686 A) (y : A) : (term103 A y c) = (term109 A c y).
Proof. exact (TRANS (@lem4822388 A c y) (@lem4822410 A c y)). Qed.
Lemma lem4822416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822417 {A : Type'} (c : type686 A) (y : A) : (term110 A y c) = (term111 A c y).
Proof. exact (MK_COMB (@lem4822416) (@lem4822415 A c y)). Qed.
Lemma lem4822420 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4822421 {A : Type'} (c : type686 A) (x : A) (y : A) : (term112 A c x y) = (term113 A c x y).
Proof. exact (MK_COMB (@lem4822417 A c y) (@lem4822420 A x y)). Qed.
Lemma lem4822424 {A : Type'} (c : type686 A) (x : A) (y : A) : (term114 A c x y) = (term115 A c x y).
Proof. exact (MK_COMB (@lem4822382 A c x) (@lem4822421 A c x y)). Qed.
Lemma lem4822427 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822428 {A : Type'} (c : type686 A) (x : A) (y : A) : (term116 A c x y) = (term117 A c x y).
Proof. exact (MK_COMB (@lem4822427) (@lem4822424 A c x y)). Qed.
Lemma lem4822429 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4822430 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) (y : A) : (term118 A c R x y) = (term119 A c R x y).
Proof. exact (MK_COMB (@lem4822428 A c x y) (@lem4822429 A R x y)). Qed.
Lemma lem4822433 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) : (term120 A c R x) = (term121 A c R x).
Proof. exact (fun_ext (fun y : A => @lem4822430 A c R x y)). Qed.
Lemma lem4822434 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822435 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) : (term122 A c R x) = (term123 A c R x).
Proof. exact (MK_COMB (@lem4822434 A) (@lem4822433 A c R x)). Qed.
Lemma lem4822440 {A : Type'} (c : type686 A) (R : type1402 A) : (term124 A c R) = (term125 A c R).
Proof. exact (fun_ext (fun x : A => @lem4822435 A c R x)). Qed.
Lemma lem4822441 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822442 {A : Type'} (c : type686 A) (R : type1402 A) : (term26 A c R) = (term126 A c R).
Proof. exact (MK_COMB (@lem4822441 A) (@lem4822440 A c R)). Qed.
Lemma lem4822447 {A : Type'} (c : type686 A) (R : type1402 A) : (term54 A c R) = (term127 A c R).
Proof. exact (MK_COMB (@lem4822337 A R c) (@lem4822442 A c R)). Qed.
Lemma lem4822450 {A : Type'} (R : type1402 A) : (term55 A R) = (term128 A R).
Proof. exact (fun_ext (fun c : type686 A => @lem4822447 A c R)). Qed.
Lemma lem4822451 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4822452 {A : Type'} (R : type1402 A) : (term56 A R) = (term129 A R).
Proof. exact (MK_COMB (@lem4822451 A) (@lem4822450 A R)). Qed.
Lemma lem4822457 {A : Type'} : (term57 A) = (term130 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem4822452 A R)). Qed.
Lemma lem4822458 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4822459 {A : Type'} : (term58 A) = (term131 A).
Proof. exact (MK_COMB (@lem4822458 A) (@lem4822457 A)). Qed.
Lemma lem4822464 {A : Type'} : (term131 A) = (term58 A).
Proof. exact (SYM (@lem4822459 A)). Qed.
Lemma lem4822466 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4822467 {A : Type'} : (term131 A) = (term133 A).
Proof. exact (@lem4822466 (term131 A)). Qed.
Lemma lem4822468 {A : Type'} : (term133 A) = (term131 A).
Proof. exact (SYM (@lem4822467 A)). Qed.
Lemma lem4822469 {A : Type'} (h1 : term134 A) : term134 A.
Proof. exact (h1). Qed.
Lemma lem4822472 {A : Type'} (h1 : term133 A) : term133 A.
Proof. exact (h1). Qed.
Lemma lem4822473 {A : Type'} : term135 A.
Proof. exact (fun h0 : term133 A => @lem4822472 A h0). Qed.
Lemma lem4822474 {A : Type'} (h1 : term135 A) : term135 A.
Proof. exact (h1). Qed.
Lemma lem4822475 {A : Type'} (h1 : term133 A) : term133 A.
Proof. exact (h1). Qed.
Lemma lem4822476 {A : Type'} (h1 : term133 A) (h2 : term135 A) : term133 A.
Proof. exact (@lem4822474 A h2 (@lem4822475 A h1)). Qed.
Lemma lem4822477 {A : Type'} (h1 : term133 A) : term136 A.
Proof. exact (fun h0 : term135 A => @lem4822476 A h1 h0). Qed.
Lemma lem4822478 {A : Type'} (h1 : term135 A) : term135 A.
Proof. exact (h1). Qed.
Lemma lem4822479 {A : Type'} (h1 : term133 A) (h2 : term135 A) : term133 A.
Proof. exact (@lem4822477 A h1 (@lem4822478 A h2)). Qed.
Lemma lem4822480 {A : Type'} (h1 : term135 A) : term135 A.
Proof. exact (fun h0 : term133 A => @lem4822479 A h0 h1). Qed.
Lemma lem4822481 {A : Type'} : term137 A.
Proof. exact (fun h0 : term135 A => @lem4822480 A h0). Qed.
Lemma lem4822484 {A : Type'} : term135 A.
Proof. exact (@lem4822481 A (@lem4822473 A)). Qed.
Lemma lem4822485 {A : Type'} : term135 A.
Proof. exact (@lem4822484 A). Qed.
Lemma lem4822487 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4822488 {A : Type'} : (term133 A) = (term138 A).
Proof. exact (@lem4822487 (term134 A)). Qed.
Lemma lem4822490 (t : Prop) : (term139 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4822491 {A : Type'} : (term138 A) = (term131 A).
Proof. exact (@lem4822490 (term131 A)). Qed.
Lemma lem4822628 {A : Type'} : (term133 A) = (term131 A).
Proof. exact (TRANS (@lem4822488 A) (@lem4822491 A)). Qed.
Lemma lem4822629 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4822632 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4822637 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term106 A c t y) = (term106 A c t y).
Proof. exact (eq_refl (term106 A c t y)). Qed.
Lemma lem4822638 {A : Type'} (c : type686 A) (y : A) : (term108 A c y) = (term108 A c y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822637 A c t y)). Qed.
Lemma lem4822639 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4822640 {A : Type'} (c : type686 A) (y : A) : (term109 A c y) = (term109 A c y).
Proof. exact (MK_COMB (@lem4822639 A) (@lem4822638 A c y)). Qed.
Lemma lem4822641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822642 {A : Type'} (c : type686 A) (y : A) : (term111 A c y) = (term111 A c y).
Proof. exact (MK_COMB (@lem4822641) (@lem4822640 A c y)). Qed.
Lemma lem4822643 {A : Type'} (c : type686 A) (x : A) (y : A) : (term113 A c x y) = (term113 A c x y).
Proof. exact (MK_COMB (@lem4822642 A c y) (@lem4822632 A x y)). Qed.
Lemma lem4822648 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term106 A c t x) = (term106 A c t x).
Proof. exact (eq_refl (term106 A c t x)). Qed.
Lemma lem4822649 {A : Type'} (c : type686 A) (x : A) : (term108 A c x) = (term108 A c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822648 A c t x)). Qed.
Lemma lem4822650 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4822651 {A : Type'} (c : type686 A) (x : A) : (term109 A c x) = (term109 A c x).
Proof. exact (MK_COMB (@lem4822650 A) (@lem4822649 A c x)). Qed.
Lemma lem4822652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822653 {A : Type'} (c : type686 A) (x : A) : (term111 A c x) = (term111 A c x).
Proof. exact (MK_COMB (@lem4822652) (@lem4822651 A c x)). Qed.
Lemma lem4822654 {A : Type'} (c : type686 A) (x : A) (y : A) : (term115 A c x y) = (term115 A c x y).
Proof. exact (MK_COMB (@lem4822653 A c x) (@lem4822643 A c x y)). Qed.
Lemma lem4822655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822656 {A : Type'} (c : type686 A) (x : A) (y : A) : (term117 A c x y) = (term117 A c x y).
Proof. exact (MK_COMB (@lem4822655) (@lem4822654 A c x y)). Qed.
Lemma lem4822657 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) (y : A) : (term119 A c R x y) = (term119 A c R x y).
Proof. exact (MK_COMB (@lem4822656 A c x y) (@lem4822629 A R x y)). Qed.
Lemma lem4822658 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) : (term121 A c R x) = (term121 A c R x).
Proof. exact (fun_ext (fun y : A => @lem4822657 A c R x y)). Qed.
Lemma lem4822659 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822660 {A : Type'} (c : type686 A) (R : type1402 A) (x : A) : (term123 A c R x) = (term123 A c R x).
Proof. exact (MK_COMB (@lem4822659 A) (@lem4822658 A c R x)). Qed.
Lemma lem4822661 {A : Type'} (c : type686 A) (R : type1402 A) : (term125 A c R) = (term125 A c R).
Proof. exact (fun_ext (fun x : A => @lem4822660 A c R x)). Qed.
Lemma lem4822662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822663 {A : Type'} (c : type686 A) (R : type1402 A) : (term126 A c R) = (term126 A c R).
Proof. exact (MK_COMB (@lem4822662 A) (@lem4822661 A c R)). Qed.
Lemma lem4822668 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term90 A t s x) = (term90 A t s x).
Proof. exact (eq_refl (term90 A t s x)). Qed.
Lemma lem4822669 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term92 A t s).
Proof. exact (fun_ext (fun x : A => @lem4822668 A t s x)). Qed.
Lemma lem4822670 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822671 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term93 A t s) = (term93 A t s).
Proof. exact (MK_COMB (@lem4822670 A) (@lem4822669 A t s)). Qed.
Lemma lem4822676 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term90 A s t x).
Proof. exact (eq_refl (term90 A s t x)). Qed.
Lemma lem4822677 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term92 A s t).
Proof. exact (fun_ext (fun x : A => @lem4822676 A s t x)). Qed.
Lemma lem4822678 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822679 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem4822678 A) (@lem4822677 A s t)). Qed.
Lemma lem4822680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822681 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term94 A s t).
Proof. exact (MK_COMB (@lem4822680) (@lem4822679 A s t)). Qed.
Lemma lem4822682 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term95 A t s).
Proof. exact (MK_COMB (@lem4822681 A s t) (@lem4822671 A t s)). Qed.
Lemma lem4822689 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term86 A s c t) = (term86 A s c t).
Proof. exact (eq_refl (term86 A s c t)). Qed.
Lemma lem4822690 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term96 A c t s) = (term96 A c t s).
Proof. exact (MK_COMB (@lem4822689 A s c t) (@lem4822682 A t s)). Qed.
Lemma lem4822691 {A : Type'} (c : type686 A) (s : A -> Prop) : (term97 A c s) = (term97 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822690 A c t s)). Qed.
Lemma lem4822692 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822693 {A : Type'} (c : type686 A) (s : A -> Prop) : (term98 A c s) = (term98 A c s).
Proof. exact (MK_COMB (@lem4822692 A) (@lem4822691 A c s)). Qed.
Lemma lem4822694 {A : Type'} (c : type686 A) : (term99 A c) = (term99 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822693 A c s)). Qed.
Lemma lem4822695 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822696 {A : Type'} (c : type686 A) : (term100 A c) = (term100 A c).
Proof. exact (MK_COMB (@lem4822695 A) (@lem4822694 A c)). Qed.
Lemma lem4822711 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term70 A s R x y) = (term70 A s R x y).
Proof. exact (eq_refl (term70 A s R x y)). Qed.
Lemma lem4822712 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term72 A s R x) = (term72 A s R x).
Proof. exact (fun_ext (fun y : A => @lem4822711 A s R x y)). Qed.
Lemma lem4822713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822714 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term74 A s R x) = (term74 A s R x).
Proof. exact (MK_COMB (@lem4822713 A) (@lem4822712 A s R x)). Qed.
Lemma lem4822715 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term76 A s R) = (term76 A s R).
Proof. exact (fun_ext (fun x : A => @lem4822714 A s R x)). Qed.
Lemma lem4822716 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822717 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term77 A s R) = (term77 A s R).
Proof. exact (MK_COMB (@lem4822716 A) (@lem4822715 A s R)). Qed.
Lemma lem4822720 {A : Type'} (c : type686 A) (s : A -> Prop) : (term59 A c s) = (term59 A c s).
Proof. exact (eq_refl (term59 A c s)). Qed.
Lemma lem4822721 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term78 A c s R) = (term78 A c s R).
Proof. exact (MK_COMB (@lem4822720 A c s) (@lem4822717 A s R)). Qed.
Lemma lem4822722 {A : Type'} (c : type686 A) (R : type1402 A) : (term79 A c R) = (term79 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822721 A c s R)). Qed.
Lemma lem4822723 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822724 {A : Type'} (c : type686 A) (R : type1402 A) : (term80 A c R) = (term80 A c R).
Proof. exact (MK_COMB (@lem4822723 A) (@lem4822722 A c R)). Qed.
Lemma lem4822725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822726 {A : Type'} (c : type686 A) (R : type1402 A) : (term81 A c R) = (term81 A c R).
Proof. exact (MK_COMB (@lem4822725) (@lem4822724 A c R)). Qed.
Lemma lem4822727 {A : Type'} (R : type1402 A) (c : type686 A) : (term101 A R c) = (term101 A R c).
Proof. exact (MK_COMB (@lem4822726 A c R) (@lem4822696 A c)). Qed.
Lemma lem4822728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4822729 {A : Type'} (R : type1402 A) (c : type686 A) : (term102 A R c) = (term102 A R c).
Proof. exact (MK_COMB (@lem4822728) (@lem4822727 A R c)). Qed.
Lemma lem4822730 {A : Type'} (c : type686 A) (R : type1402 A) : (term127 A c R) = (term127 A c R).
Proof. exact (MK_COMB (@lem4822729 A R c) (@lem4822663 A c R)). Qed.
Lemma lem4822731 {A : Type'} (R : type1402 A) : (term128 A R) = (term128 A R).
Proof. exact (fun_ext (fun c : type686 A => @lem4822730 A c R)). Qed.
Lemma lem4822732 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4822733 {A : Type'} (R : type1402 A) : (term129 A R) = (term129 A R).
Proof. exact (MK_COMB (@lem4822732 A) (@lem4822731 A R)). Qed.
Lemma lem4822734 {A : Type'} : (term130 A) = (term130 A).
Proof. exact (fun_ext (fun R : type1402 A => @lem4822733 A R)). Qed.
Lemma lem4822735 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4822736 {A : Type'} : (term131 A) = (term131 A).
Proof. exact (MK_COMB (@lem4822735 A) (@lem4822734 A)). Qed.
Lemma lem4822849 {A : Type'} : (term133 A) = (term131 A).
Proof. exact (TRANS (@lem4822628 A) (@lem4822736 A)). Qed.
Lemma lem4822850 {A : Type'} : (term131 A) = (term133 A).
Proof. exact (SYM (@lem4822849 A)). Qed.
Lemma lem4822851 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term101 A R c.
Proof. exact (h1). Qed.
Lemma lem4822852 {A : Type'} (c : type686 A) (x : A) (y : A) (h1 : term115 A c x y) : term115 A c x y.
Proof. exact (h1). Qed.
Lemma lem4822854 (p : Prop) : p = (term132 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4822855 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term140 A R x y).
Proof. exact (@lem4822854 (R x y)). Qed.
Lemma lem4822856 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term140 A R x y) = (R x y).
Proof. exact (SYM (@lem4822855 A R x y)). Qed.
Lemma lem4822857 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term141 A R x y.
Proof. exact (h1). Qed.
Lemma lem4822863 {A : Type'} (x : A) (y : A) : (term142 A x y) = (x = y).
Proof. exact (@lem16933 (x = y)). Qed.
Lemma lem4822865 {A : Type'} (s : A -> Prop) (y : A) : (term143 A s y) = (term143 A s y).
Proof. exact (eq_refl (term143 A s y)). Qed.
Lemma lem4822866 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term144 A s x y) = (term145 A s x y).
Proof. exact (MK_COMB (@lem4822865 A s y) (@lem4822863 A x y)). Qed.
Lemma lem4822867 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term146 A s x y) = (term144 A s x y).
Proof. exact (@lem17045 (s y) (term62 A x y)). Qed.
Lemma lem4822868 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term146 A s x y) = (term145 A s x y).
Proof. exact (TRANS (@lem4822867 A s x y) (@lem4822866 A s x y)). Qed.
Lemma lem4822870 {A : Type'} (s : A -> Prop) (x : A) : (term143 A s x) = (term143 A s x).
Proof. exact (eq_refl (term143 A s x)). Qed.
Lemma lem4822871 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term147 A s x y) = (term148 A s x y).
Proof. exact (MK_COMB (@lem4822870 A s x) (@lem4822868 A s x y)). Qed.
Lemma lem4822872 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term149 A s x y) = (term147 A s x y).
Proof. exact (@lem17045 (s x) (term64 A s x y)). Qed.
Lemma lem4822873 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term149 A s x y) = (term148 A s x y).
Proof. exact (TRANS (@lem4822872 A s x y) (@lem4822871 A s x y)). Qed.
Lemma lem4822874 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem4822875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822876 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term150 A s x y) = (term151 A s x y).
Proof. exact (MK_COMB (@lem4822875) (@lem4822873 A s x y)). Qed.
Lemma lem4822877 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term152 A s R x y) = (term153 A s R x y).
Proof. exact (MK_COMB (@lem4822876 A s x y) (@lem4822874 A R x y)). Qed.
Lemma lem4822878 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term70 A s R x y) = (term152 A s R x y).
Proof. exact (@lem17265 (term66 A s x y) (R x y)). Qed.
Lemma lem4822879 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term70 A s R x y) = (term153 A s R x y).
Proof. exact (TRANS (@lem4822878 A s R x y) (@lem4822877 A s R x y)). Qed.
Lemma lem4822880 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term72 A s R x) = (term154 A s R x).
Proof. exact (fun_ext (fun y : A => @lem4822879 A s R x y)). Qed.
Lemma lem4822881 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822882 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term74 A s R x) = (term155 A s R x).
Proof. exact (MK_COMB (@lem4822881 A) (@lem4822880 A s R x)). Qed.
Lemma lem4822883 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term76 A s R) = (term156 A s R).
Proof. exact (fun_ext (fun x : A => @lem4822882 A s R x)). Qed.
Lemma lem4822884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822885 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term77 A s R) = (term157 A s R).
Proof. exact (MK_COMB (@lem4822884 A) (@lem4822883 A s R)). Qed.
Lemma lem4822887 {A : Type'} (c : type686 A) (s : A -> Prop) : (term158 A c s) = (term158 A c s).
Proof. exact (eq_refl (term158 A c s)). Qed.
Lemma lem4822888 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term159 A c s R) = (term160 A c s R).
Proof. exact (MK_COMB (@lem4822887 A c s) (@lem4822885 A s R)). Qed.
Lemma lem4822889 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term78 A c s R) = (term159 A c s R).
Proof. exact (@lem17265 (c s) (term77 A s R)). Qed.
Lemma lem4822890 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term78 A c s R) = (term160 A c s R).
Proof. exact (TRANS (@lem4822889 A c s R) (@lem4822888 A c s R)). Qed.
Lemma lem4822891 {A : Type'} (c : type686 A) (R : type1402 A) : (term79 A c R) = (term161 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822890 A c s R)). Qed.
Lemma lem4822892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822893 {A : Type'} (c : type686 A) (R : type1402 A) : (term80 A c R) = (term162 A c R).
Proof. exact (MK_COMB (@lem4822892 A) (@lem4822891 A c R)). Qed.
Lemma lem4822900 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term163 A s c t) = (term164 A s c t).
Proof. exact (@lem17045 (c s) (c t)). Qed.
Lemma lem4822907 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term90 A s t x) = (term165 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem4822908 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term166 A s t).
Proof. exact (fun_ext (fun x : A => @lem4822907 A s t x)). Qed.
Lemma lem4822909 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822910 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term167 A s t).
Proof. exact (MK_COMB (@lem4822909 A) (@lem4822908 A s t)). Qed.
Lemma lem4822917 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term90 A t s x) = (term165 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4822918 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term92 A t s) = (term166 A t s).
Proof. exact (fun_ext (fun x : A => @lem4822917 A t s x)). Qed.
Lemma lem4822919 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4822920 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term93 A t s) = (term167 A t s).
Proof. exact (MK_COMB (@lem4822919 A) (@lem4822918 A t s)). Qed.
Lemma lem4822921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term168 A s t).
Proof. exact (MK_COMB (@lem4822921) (@lem4822910 A s t)). Qed.
Lemma lem4822923 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term169 A t s).
Proof. exact (MK_COMB (@lem4822922 A s t) (@lem4822920 A t s)). Qed.
Lemma lem4822924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4822925 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term170 A s c t) = (term171 A s c t).
Proof. exact (MK_COMB (@lem4822924) (@lem4822900 A s c t)). Qed.
Lemma lem4822926 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term172 A c t s) = (term173 A c t s).
Proof. exact (MK_COMB (@lem4822925 A s c t) (@lem4822923 A t s)). Qed.
Lemma lem4822927 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term96 A c t s) = (term172 A c t s).
Proof. exact (@lem17265 (term85 A s c t) (term95 A t s)). Qed.
Lemma lem4822928 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term96 A c t s) = (term173 A c t s).
Proof. exact (TRANS (@lem4822927 A c t s) (@lem4822926 A c t s)). Qed.
Lemma lem4822929 {A : Type'} (c : type686 A) (s : A -> Prop) : (term97 A c s) = (term174 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4822928 A c t s)). Qed.
Lemma lem4822930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822931 {A : Type'} (c : type686 A) (s : A -> Prop) : (term98 A c s) = (term175 A c s).
Proof. exact (MK_COMB (@lem4822930 A) (@lem4822929 A c s)). Qed.
Lemma lem4822932 {A : Type'} (c : type686 A) : (term99 A c) = (term176 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4822931 A c s)). Qed.
Lemma lem4822933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4822934 {A : Type'} (c : type686 A) : (term100 A c) = (term177 A c).
Proof. exact (MK_COMB (@lem4822933 A) (@lem4822932 A c)). Qed.
Lemma lem4822935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4822936 {A : Type'} (c : type686 A) (R : type1402 A) : (term81 A c R) = (term178 A c R).
Proof. exact (MK_COMB (@lem4822935) (@lem4822893 A c R)). Qed.
Lemma lem4823157 {A : Type'} (R : type1402 A) (c : type686 A) : (term101 A R c) = (term179 A R c).
Proof. exact (MK_COMB (@lem4822936 A c R) (@lem4822934 A c)). Qed.
Lemma lem4823158 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term179 A R c.
Proof. exact (EQ_MP (@lem4823157 A R c) (@lem4822851 A R c h1)). Qed.
Lemma lem4823163 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term106 A c t x) = (term106 A c t x).
Proof. exact (eq_refl (term106 A c t x)). Qed.
Lemma lem4823164 {A : Type'} (c : type686 A) (x : A) : (term108 A c x) = (term108 A c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823163 A c t x)). Qed.
Lemma lem4823165 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823166 {A : Type'} (c : type686 A) (x : A) : (term109 A c x) = (term109 A c x).
Proof. exact (MK_COMB (@lem4823165 A) (@lem4823164 A c x)). Qed.
Lemma lem4823171 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term106 A c t y) = (term106 A c t y).
Proof. exact (eq_refl (term106 A c t y)). Qed.
Lemma lem4823172 {A : Type'} (c : type686 A) (y : A) : (term108 A c y) = (term108 A c y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823171 A c t y)). Qed.
Lemma lem4823173 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823174 {A : Type'} (c : type686 A) (y : A) : (term109 A c y) = (term109 A c y).
Proof. exact (MK_COMB (@lem4823173 A) (@lem4823172 A c y)). Qed.
Lemma lem4823175 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4823176 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823177 {A : Type'} (c : type686 A) (y : A) : (term111 A c y) = (term111 A c y).
Proof. exact (MK_COMB (@lem4823176) (@lem4823174 A c y)). Qed.
Lemma lem4823178 {A : Type'} (c : type686 A) (x : A) (y : A) : (term113 A c x y) = (term113 A c x y).
Proof. exact (MK_COMB (@lem4823177 A c y) (@lem4823175 A x y)). Qed.
Lemma lem4823179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823180 {A : Type'} (c : type686 A) (x : A) : (term111 A c x) = (term111 A c x).
Proof. exact (MK_COMB (@lem4823179) (@lem4823166 A c x)). Qed.
Lemma lem4823181 {A : Type'} (c : type686 A) (x : A) (y : A) : (term115 A c x y) = (term115 A c x y).
Proof. exact (MK_COMB (@lem4823180 A c x) (@lem4823178 A c x y)). Qed.
Lemma lem4823240 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4823241 {A : Type'} (P : type686 A) (Q : Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (@lem4823240 (A -> Prop) P Q). Qed.
Lemma lem4823242 {A : Type'} (c : type686 A) (x : A) (y : A) : (term184 A c x y) = (term185 A c x y).
Proof. exact (@lem4823241 A (term108 A c y) (term62 A x y)). Qed.
Lemma lem4823243 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term186 A c y t) = (term106 A c t y).
Proof. exact (eq_refl (term186 A c y t)). Qed.
Lemma lem4823244 {A : Type'} (c : type686 A) (y : A) : (term187 A c y) = (term108 A c y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823243 A c t y)). Qed.
Lemma lem4823245 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823246 {A : Type'} (c : type686 A) (y : A) : (term188 A c y) = (term109 A c y).
Proof. exact (MK_COMB (@lem4823245 A) (@lem4823244 A c y)). Qed.
Lemma lem4823247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823248 {A : Type'} (c : type686 A) (y : A) : (term189 A c y) = (term111 A c y).
Proof. exact (MK_COMB (@lem4823247) (@lem4823246 A c y)). Qed.
Lemma lem4823249 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4823250 {A : Type'} (c : type686 A) (x : A) (y : A) : (term184 A c x y) = (term113 A c x y).
Proof. exact (MK_COMB (@lem4823248 A c y) (@lem4823249 A x y)). Qed.
Lemma lem4823251 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823252 {A : Type'} (c : type686 A) (x : A) (y : A) : (term190 A c x y) = (term191 A c x y).
Proof. exact (MK_COMB (@lem4823251) (@lem4823250 A c x y)). Qed.
Lemma lem4823253 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term186 A c y t) = (term106 A c t y).
Proof. exact (eq_refl (term186 A c y t)). Qed.
Lemma lem4823254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823255 {A : Type'} (c : type686 A) (t : A -> Prop) (y : A) : (term192 A c y t) = (term193 A c t y).
Proof. exact (MK_COMB (@lem4823254) (@lem4823253 A c t y)). Qed.
Lemma lem4823256 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4823257 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) (y : A) : (term194 A c t x y) = (term195 A c t x y).
Proof. exact (MK_COMB (@lem4823255 A c t y) (@lem4823256 A x y)). Qed.
Lemma lem4823258 {A : Type'} (c : type686 A) (x : A) (y : A) : (term196 A c x y) = (term197 A c x y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823257 A c t x y)). Qed.
Lemma lem4823259 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823260 {A : Type'} (c : type686 A) (x : A) (y : A) : (term185 A c x y) = (term198 A c x y).
Proof. exact (MK_COMB (@lem4823259 A) (@lem4823258 A c x y)). Qed.
Lemma lem4823261 {A : Type'} (c : type686 A) (x : A) (y : A) : ((term184 A c x y) = (term185 A c x y)) = ((term113 A c x y) = (term198 A c x y)).
Proof. exact (MK_COMB (@lem4823252 A c x y) (@lem4823260 A c x y)). Qed.
Lemma lem4823262 {A : Type'} (c : type686 A) (x : A) (y : A) : (term113 A c x y) = (term198 A c x y).
Proof. exact (EQ_MP (@lem4823261 A c x y) (@lem4823242 A c x y)). Qed.
Lemma lem4823263 {A : Type'} (c : type686 A) (x : A) : (term111 A c x) = (term111 A c x).
Proof. exact (eq_refl (term111 A c x)). Qed.
Lemma lem4823264 {A : Type'} (c : type686 A) (x : A) (y : A) : (term115 A c x y) = (term199 A c x y).
Proof. exact (MK_COMB (@lem4823263 A c x) (@lem4823262 A c x y)). Qed.
Lemma lem4823266 {A : Type'} (P : A -> Prop) (Q : Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4823267 {A : Type'} (P : type686 A) (Q : Prop) : (term182 A P Q) = (term183 A P Q).
Proof. exact (@lem4823266 (A -> Prop) P Q). Qed.
Lemma lem4823268 {A : Type'} (c : type686 A) (x : A) (y : A) : (term200 A c x y) = (term201 A c x y).
Proof. exact (@lem4823267 A (term108 A c x) (term198 A c x y)). Qed.
Lemma lem4823269 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term186 A c x t) = (term106 A c t x).
Proof. exact (eq_refl (term186 A c x t)). Qed.
Lemma lem4823270 {A : Type'} (c : type686 A) (x : A) : (term187 A c x) = (term108 A c x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823269 A c t x)). Qed.
Lemma lem4823271 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823272 {A : Type'} (c : type686 A) (x : A) : (term188 A c x) = (term109 A c x).
Proof. exact (MK_COMB (@lem4823271 A) (@lem4823270 A c x)). Qed.
Lemma lem4823273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823274 {A : Type'} (c : type686 A) (x : A) : (term189 A c x) = (term111 A c x).
Proof. exact (MK_COMB (@lem4823273) (@lem4823272 A c x)). Qed.
Lemma lem4823275 {A : Type'} (c : type686 A) (x : A) (y : A) : (term198 A c x y) = (term198 A c x y).
Proof. exact (eq_refl (term198 A c x y)). Qed.
Lemma lem4823276 {A : Type'} (c : type686 A) (x : A) (y : A) : (term200 A c x y) = (term199 A c x y).
Proof. exact (MK_COMB (@lem4823274 A c x) (@lem4823275 A c x y)). Qed.
Lemma lem4823277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823278 {A : Type'} (c : type686 A) (x : A) (y : A) : (term202 A c x y) = (term203 A c x y).
Proof. exact (MK_COMB (@lem4823277) (@lem4823276 A c x y)). Qed.
Lemma lem4823279 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term186 A c x t) = (term106 A c t x).
Proof. exact (eq_refl (term186 A c x t)). Qed.
Lemma lem4823280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823281 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term192 A c x t) = (term193 A c t x).
Proof. exact (MK_COMB (@lem4823280) (@lem4823279 A c t x)). Qed.
Lemma lem4823282 {A : Type'} (c : type686 A) (x : A) (y : A) : (term198 A c x y) = (term198 A c x y).
Proof. exact (eq_refl (term198 A c x y)). Qed.
Lemma lem4823283 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term204 A t c x y) = (term205 A t c x y).
Proof. exact (MK_COMB (@lem4823281 A c t x) (@lem4823282 A c x y)). Qed.
Lemma lem4823284 {A : Type'} (c : type686 A) (x : A) (y : A) : (term206 A c x y) = (term207 A c x y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823283 A t c x y)). Qed.
Lemma lem4823285 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823286 {A : Type'} (c : type686 A) (x : A) (y : A) : (term201 A c x y) = (term208 A c x y).
Proof. exact (MK_COMB (@lem4823285 A) (@lem4823284 A c x y)). Qed.
Lemma lem4823287 {A : Type'} (c : type686 A) (x : A) (y : A) : ((term200 A c x y) = (term201 A c x y)) = ((term199 A c x y) = (term208 A c x y)).
Proof. exact (MK_COMB (@lem4823278 A c x y) (@lem4823286 A c x y)). Qed.
Lemma lem4823288 {A : Type'} (c : type686 A) (x : A) (y : A) : (term199 A c x y) = (term208 A c x y).
Proof. exact (EQ_MP (@lem4823287 A c x y) (@lem4823268 A c x y)). Qed.
Lemma lem4823290 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4823291 {A : Type'} (P : Prop) (Q : type686 A) : (term211 A P Q) = (term212 A P Q).
Proof. exact (@lem4823290 (A -> Prop) P Q). Qed.
Lemma lem4823292 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term213 A t c x y) = (term214 A t c x y).
Proof. exact (@lem4823291 A (term106 A c t x) (term197 A c x y)). Qed.
Lemma lem4823293 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) (y : A) : (term215 A c x y t) = (term195 A c t x y).
Proof. exact (eq_refl (term215 A c x y t)). Qed.
Lemma lem4823294 {A : Type'} (c : type686 A) (x : A) (y : A) : (term216 A c x y) = (term197 A c x y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823293 A c t x y)). Qed.
Lemma lem4823295 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823296 {A : Type'} (c : type686 A) (x : A) (y : A) : (term217 A c x y) = (term198 A c x y).
Proof. exact (MK_COMB (@lem4823295 A) (@lem4823294 A c x y)). Qed.
Lemma lem4823297 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term193 A c t x) = (term193 A c t x).
Proof. exact (eq_refl (term193 A c t x)). Qed.
Lemma lem4823298 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term213 A t c x y) = (term205 A t c x y).
Proof. exact (MK_COMB (@lem4823297 A c t x) (@lem4823296 A c x y)). Qed.
Lemma lem4823299 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823300 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term218 A t c x y) = (term219 A t c x y).
Proof. exact (MK_COMB (@lem4823299) (@lem4823298 A t c x y)). Qed.
Lemma lem4823301 {A : Type'} (c : type686 A) (t' : A -> Prop) (x : A) (y : A) : (term215 A c x y t') = (term195 A c t' x y).
Proof. exact (eq_refl (term215 A c x y t')). Qed.
Lemma lem4823302 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term193 A c t x) = (term193 A c t x).
Proof. exact (eq_refl (term193 A c t x)). Qed.
Lemma lem4823303 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) : (term220 A t c x y t') = (term221 A t c t' x y).
Proof. exact (MK_COMB (@lem4823302 A c t x) (@lem4823301 A c t' x y)). Qed.
Lemma lem4823304 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term222 A t c x y) = (term223 A t c x y).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4823303 A t c t' x y)). Qed.
Lemma lem4823305 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823306 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term214 A t c x y) = (term224 A t c x y).
Proof. exact (MK_COMB (@lem4823305 A) (@lem4823304 A t c x y)). Qed.
Lemma lem4823307 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : ((term213 A t c x y) = (term214 A t c x y)) = ((term205 A t c x y) = (term224 A t c x y)).
Proof. exact (MK_COMB (@lem4823300 A t c x y) (@lem4823306 A t c x y)). Qed.
Lemma lem4823308 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) : (term205 A t c x y) = (term224 A t c x y).
Proof. exact (EQ_MP (@lem4823307 A t c x y) (@lem4823292 A t c x y)). Qed.
Lemma lem4823309 {A : Type'} (c : type686 A) (x : A) (y : A) : (term207 A c x y) = (term225 A c x y).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823308 A t c x y)). Qed.
Lemma lem4823310 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4823311 {A : Type'} (c : type686 A) (x : A) (y : A) : (term208 A c x y) = (term226 A c x y).
Proof. exact (MK_COMB (@lem4823310 A) (@lem4823309 A c x y)). Qed.
Lemma lem4823312 {A : Type'} (c : type686 A) (x : A) (y : A) : (term199 A c x y) = (term226 A c x y).
Proof. exact (TRANS (@lem4823288 A c x y) (@lem4823311 A c x y)). Qed.
Lemma lem4823314 {A : Type'} (c : type686 A) (x : A) (y : A) : (term115 A c x y) = (term226 A c x y).
Proof. exact (TRANS (@lem4823264 A c x y) (@lem4823312 A c x y)). Qed.
Lemma lem4823315 {A : Type'} (c : type686 A) (x : A) (y : A) : (term115 A c x y) = (term226 A c x y).
Proof. exact (TRANS (@lem4823181 A c x y) (@lem4823314 A c x y)). Qed.
Lemma lem4823316 {A : Type'} (c : type686 A) (x : A) (y : A) (h1 : term115 A c x y) : term226 A c x y.
Proof. exact (EQ_MP (@lem4823315 A c x y) (@lem4822852 A c x y h1)). Qed.
Lemma lem4823322 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term141 A R x y.
Proof. exact (h1). Qed.
Lemma lem4823323 {A : Type'} (t : A -> Prop) (c : type686 A) (x : A) (y : A) (h1 : term224 A t c x y) : term224 A t c x y.
Proof. exact (h1). Qed.
Lemma lem4823324 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term221 A t c t' x y.
Proof. exact (h1). Qed.
Lemma lem4823329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823330 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823329 A Prop f x). Qed.
Lemma lem4823332 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4823330 A s x). Qed.
Lemma lem4823333 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823338 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823339 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823338 A Prop f x). Qed.
Lemma lem4823341 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4823339 A t x). Qed.
Lemma lem4823342 {A : Type'} (t : A -> Prop) (x : A) : (term227 A t x) = (term228 A t x).
Proof. exact (MK_COMB (@lem4823333) (@lem4823341 A t x)). Qed.
Lemma lem4823343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823344 {A : Type'} (t : A -> Prop) (x : A) : (term143 A t x) = (term229 A t x).
Proof. exact (MK_COMB (@lem4823343) (@lem4823342 A t x)). Qed.
Lemma lem4823345 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term165 A t s x) = (term230 A t s x).
Proof. exact (MK_COMB (@lem4823344 A t x) (@lem4823332 A s x)). Qed.
Lemma lem4823346 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term166 A t s) = (term231 A t s).
Proof. exact (fun_ext (fun x : A => @lem4823345 A t s x)). Qed.
Lemma lem4823347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823348 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term167 A t s) = (term232 A t s).
Proof. exact (MK_COMB (@lem4823347 A) (@lem4823346 A t s)). Qed.
Lemma lem4823353 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823354 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823353 A Prop f x). Qed.
Lemma lem4823356 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4823354 A t x). Qed.
Lemma lem4823357 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823362 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823363 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823362 A Prop f x). Qed.
Lemma lem4823365 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4823363 A s x). Qed.
Lemma lem4823366 {A : Type'} (s : A -> Prop) (x : A) : (term227 A s x) = (term228 A s x).
Proof. exact (MK_COMB (@lem4823357) (@lem4823365 A s x)). Qed.
Lemma lem4823367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823368 {A : Type'} (s : A -> Prop) (x : A) : (term143 A s x) = (term229 A s x).
Proof. exact (MK_COMB (@lem4823367) (@lem4823366 A s x)). Qed.
Lemma lem4823369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term165 A s t x) = (term230 A s t x).
Proof. exact (MK_COMB (@lem4823368 A s x) (@lem4823356 A t x)). Qed.
Lemma lem4823370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term166 A s t) = (term231 A s t).
Proof. exact (fun_ext (fun x : A => @lem4823369 A s t x)). Qed.
Lemma lem4823371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823372 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term167 A s t) = (term232 A s t).
Proof. exact (MK_COMB (@lem4823371 A) (@lem4823370 A s t)). Qed.
Lemma lem4823373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823374 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term168 A s t) = (term233 A s t).
Proof. exact (MK_COMB (@lem4823373) (@lem4823372 A s t)). Qed.
Lemma lem4823375 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term169 A t s) = (term234 A t s).
Proof. exact (MK_COMB (@lem4823374 A s t) (@lem4823348 A t s)). Qed.
Lemma lem4823376 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823381 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823382 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4823381 (A -> Prop) Prop f x). Qed.
Lemma lem4823384 {A : Type'} (c : type686 A) (t : A -> Prop) : (c t) = (@I ((A -> Prop) -> Prop) c t).
Proof. exact (@lem4823382 A c t). Qed.
Lemma lem4823385 {A : Type'} (c : type686 A) (t : A -> Prop) : (term235 A c t) = (term236 A c t).
Proof. exact (MK_COMB (@lem4823376) (@lem4823384 A c t)). Qed.
Lemma lem4823386 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823392 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4823391 (A -> Prop) Prop f x). Qed.
Lemma lem4823394 {A : Type'} (c : type686 A) (s : A -> Prop) : (c s) = (@I ((A -> Prop) -> Prop) c s).
Proof. exact (@lem4823392 A c s). Qed.
Lemma lem4823395 {A : Type'} (c : type686 A) (s : A -> Prop) : (term235 A c s) = (term236 A c s).
Proof. exact (MK_COMB (@lem4823386) (@lem4823394 A c s)). Qed.
Lemma lem4823396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823397 {A : Type'} (c : type686 A) (s : A -> Prop) : (term158 A c s) = (term237 A c s).
Proof. exact (MK_COMB (@lem4823396) (@lem4823395 A c s)). Qed.
Lemma lem4823398 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term164 A s c t) = (term238 A s c t).
Proof. exact (MK_COMB (@lem4823397 A c s) (@lem4823385 A c t)). Qed.
Lemma lem4823399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823400 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term171 A s c t) = (term239 A s c t).
Proof. exact (MK_COMB (@lem4823399) (@lem4823398 A s c t)). Qed.
Lemma lem4823401 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term173 A c t s) = (term240 A c t s).
Proof. exact (MK_COMB (@lem4823400 A s c t) (@lem4823375 A t s)). Qed.
Lemma lem4823402 {A : Type'} (c : type686 A) (s : A -> Prop) : (term174 A c s) = (term241 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823401 A c t s)). Qed.
Lemma lem4823403 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823404 {A : Type'} (c : type686 A) (s : A -> Prop) : (term175 A c s) = (term242 A c s).
Proof. exact (MK_COMB (@lem4823403 A) (@lem4823402 A c s)). Qed.
Lemma lem4823405 {A : Type'} (c : type686 A) : (term176 A c) = (term243 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823404 A c s)). Qed.
Lemma lem4823406 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823407 {A : Type'} (c : type686 A) : (term177 A c) = (term244 A c).
Proof. exact (MK_COMB (@lem4823406 A) (@lem4823405 A c)). Qed.
Lemma lem4823414 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823415 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4823414 A (A -> Prop) f x). Qed.
Lemma lem4823416 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem4823415 A R x). Qed.
Lemma lem4823417 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4823418 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem4823416 A R x) (@lem4823417 A y)). Qed.
Lemma lem4823420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823421 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823420 A Prop f x). Qed.
Lemma lem4823422 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term245 A R x y).
Proof. exact (@lem4823421 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem4823424 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term245 A R x y).
Proof. exact (TRANS (@lem4823418 A R x y) (@lem4823422 A R x y)). Qed.
Lemma lem4823429 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem4823430 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823435 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823436 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823435 A Prop f x). Qed.
Lemma lem4823438 {A : Type'} (s : A -> Prop) (y : A) : (s y) = (@I (A -> Prop) s y).
Proof. exact (@lem4823436 A s y). Qed.
Lemma lem4823439 {A : Type'} (s : A -> Prop) (y : A) : (term227 A s y) = (term228 A s y).
Proof. exact (MK_COMB (@lem4823430) (@lem4823438 A s y)). Qed.
Lemma lem4823440 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823441 {A : Type'} (s : A -> Prop) (y : A) : (term143 A s y) = (term229 A s y).
Proof. exact (MK_COMB (@lem4823440) (@lem4823439 A s y)). Qed.
Lemma lem4823442 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term145 A s x y) = (term246 A s x y).
Proof. exact (MK_COMB (@lem4823441 A s y) (@lem4823429 A x y)). Qed.
Lemma lem4823443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823448 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823449 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823448 A Prop f x). Qed.
Lemma lem4823451 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4823449 A s x). Qed.
Lemma lem4823452 {A : Type'} (s : A -> Prop) (x : A) : (term227 A s x) = (term228 A s x).
Proof. exact (MK_COMB (@lem4823443) (@lem4823451 A s x)). Qed.
Lemma lem4823453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823454 {A : Type'} (s : A -> Prop) (x : A) : (term143 A s x) = (term229 A s x).
Proof. exact (MK_COMB (@lem4823453) (@lem4823452 A s x)). Qed.
Lemma lem4823455 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term148 A s x y) = (term247 A s x y).
Proof. exact (MK_COMB (@lem4823454 A s x) (@lem4823442 A s x y)). Qed.
Lemma lem4823456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823457 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term151 A s x y) = (term248 A s x y).
Proof. exact (MK_COMB (@lem4823456) (@lem4823455 A s x y)). Qed.
Lemma lem4823458 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term153 A s R x y) = (term249 A s R x y).
Proof. exact (MK_COMB (@lem4823457 A s x y) (@lem4823424 A R x y)). Qed.
Lemma lem4823459 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term154 A s R x) = (term250 A s R x).
Proof. exact (fun_ext (fun y : A => @lem4823458 A s R x y)). Qed.
Lemma lem4823460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823461 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term155 A s R x) = (term251 A s R x).
Proof. exact (MK_COMB (@lem4823460 A) (@lem4823459 A s R x)). Qed.
Lemma lem4823462 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term156 A s R) = (term252 A s R).
Proof. exact (fun_ext (fun x : A => @lem4823461 A s R x)). Qed.
Lemma lem4823463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823464 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term157 A s R) = (term253 A s R).
Proof. exact (MK_COMB (@lem4823463 A) (@lem4823462 A s R)). Qed.
Lemma lem4823465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823471 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4823470 (A -> Prop) Prop f x). Qed.
Lemma lem4823473 {A : Type'} (c : type686 A) (s : A -> Prop) : (c s) = (@I ((A -> Prop) -> Prop) c s).
Proof. exact (@lem4823471 A c s). Qed.
Lemma lem4823474 {A : Type'} (c : type686 A) (s : A -> Prop) : (term235 A c s) = (term236 A c s).
Proof. exact (MK_COMB (@lem4823465) (@lem4823473 A c s)). Qed.
Lemma lem4823475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823476 {A : Type'} (c : type686 A) (s : A -> Prop) : (term158 A c s) = (term237 A c s).
Proof. exact (MK_COMB (@lem4823475) (@lem4823474 A c s)). Qed.
Lemma lem4823477 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term160 A c s R) = (term254 A c s R).
Proof. exact (MK_COMB (@lem4823476 A c s) (@lem4823464 A s R)). Qed.
Lemma lem4823478 {A : Type'} (c : type686 A) (R : type1402 A) : (term161 A c R) = (term255 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823477 A c s R)). Qed.
Lemma lem4823479 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823480 {A : Type'} (c : type686 A) (R : type1402 A) : (term162 A c R) = (term256 A c R).
Proof. exact (MK_COMB (@lem4823479 A) (@lem4823478 A c R)). Qed.
Lemma lem4823481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823482 {A : Type'} (c : type686 A) (R : type1402 A) : (term178 A c R) = (term257 A c R).
Proof. exact (MK_COMB (@lem4823481) (@lem4823480 A c R)). Qed.
Lemma lem4823483 {A : Type'} (R : type1402 A) (c : type686 A) : (term179 A R c) = (term258 A R c).
Proof. exact (MK_COMB (@lem4823482 A c R) (@lem4823407 A c)). Qed.
Lemma lem4823484 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term258 A R c.
Proof. exact (EQ_MP (@lem4823483 A R c) (@lem4823158 A R c h1)). Qed.
Lemma lem4823485 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4823492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823493 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4823492 A (A -> Prop) f x). Qed.
Lemma lem4823494 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem4823493 A R x). Qed.
Lemma lem4823495 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4823496 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem4823494 A R x) (@lem4823495 A y)). Qed.
Lemma lem4823498 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823499 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823498 A Prop f x). Qed.
Lemma lem4823500 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term245 A R x y).
Proof. exact (@lem4823499 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem4823502 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term245 A R x y).
Proof. exact (TRANS (@lem4823496 A R x y) (@lem4823500 A R x y)). Qed.
Lemma lem4823503 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term141 A R x y) = (term259 A R x y).
Proof. exact (MK_COMB (@lem4823485) (@lem4823502 A R x y)). Qed.
Lemma lem4823511 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term62 A x y).
Proof. exact (eq_refl (term62 A x y)). Qed.
Lemma lem4823516 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823517 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823516 A Prop f x). Qed.
Lemma lem4823519 {A : Type'} (t' : A -> Prop) (y : A) : (t' y) = (@I (A -> Prop) t' y).
Proof. exact (@lem4823517 A t' y). Qed.
Lemma lem4823524 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823525 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4823524 (A -> Prop) Prop f x). Qed.
Lemma lem4823527 {A : Type'} (c : type686 A) (t' : A -> Prop) : (c t') = (@I ((A -> Prop) -> Prop) c t').
Proof. exact (@lem4823525 A c t'). Qed.
Lemma lem4823528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823529 {A : Type'} (c : type686 A) (t' : A -> Prop) : (term83 A c t') = (term260 A c t').
Proof. exact (MK_COMB (@lem4823528) (@lem4823527 A c t')). Qed.
Lemma lem4823530 {A : Type'} (c : type686 A) (t' : A -> Prop) (y : A) : (term106 A c t' y) = (term261 A c t' y).
Proof. exact (MK_COMB (@lem4823529 A c t') (@lem4823519 A t' y)). Qed.
Lemma lem4823531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823532 {A : Type'} (c : type686 A) (t' : A -> Prop) (y : A) : (term193 A c t' y) = (term262 A c t' y).
Proof. exact (MK_COMB (@lem4823531) (@lem4823530 A c t' y)). Qed.
Lemma lem4823533 {A : Type'} (c : type686 A) (t' : A -> Prop) (x : A) (y : A) : (term195 A c t' x y) = (term263 A c t' x y).
Proof. exact (MK_COMB (@lem4823532 A c t' y) (@lem4823511 A x y)). Qed.
Lemma lem4823538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823539 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4823538 A Prop f x). Qed.
Lemma lem4823541 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4823539 A t x). Qed.
Lemma lem4823546 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4823547 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4823546 (A -> Prop) Prop f x). Qed.
Lemma lem4823549 {A : Type'} (c : type686 A) (t : A -> Prop) : (c t) = (@I ((A -> Prop) -> Prop) c t).
Proof. exact (@lem4823547 A c t). Qed.
Lemma lem4823550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823551 {A : Type'} (c : type686 A) (t : A -> Prop) : (term83 A c t) = (term260 A c t).
Proof. exact (MK_COMB (@lem4823550) (@lem4823549 A c t)). Qed.
Lemma lem4823552 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term106 A c t x) = (term261 A c t x).
Proof. exact (MK_COMB (@lem4823551 A c t) (@lem4823541 A t x)). Qed.
Lemma lem4823553 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4823554 {A : Type'} (c : type686 A) (t : A -> Prop) (x : A) : (term193 A c t x) = (term262 A c t x).
Proof. exact (MK_COMB (@lem4823553) (@lem4823552 A c t x)). Qed.
Lemma lem4823555 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) : (term221 A t c t' x y) = (term264 A t c t' x y).
Proof. exact (MK_COMB (@lem4823554 A c t x) (@lem4823533 A c t' x y)). Qed.
Lemma lem4823556 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term264 A t c t' x y.
Proof. exact (EQ_MP (@lem4823555 A t c t' x y) (@lem4823324 A t c t' x y h1)). Qed.
Lemma lem4823557 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term263 A c t' x y.
Proof. exact (proj2 (@lem4823556 A t c t' x y h1)). Qed.
Lemma lem4823558 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term261 A c t x.
Proof. exact (proj1 (@lem4823556 A t c t' x y h1)). Qed.
Lemma lem4823560 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term261 A c t' y.
Proof. exact (proj1 (@lem4823557 A t c t' x y h1)). Qed.
Lemma lem4823565 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term244 A c.
Proof. exact (proj2 (@lem4823484 A R c h1)). Qed.
Lemma lem4823566 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term256 A c R.
Proof. exact (proj1 (@lem4823484 A R c h1)). Qed.
Lemma lem4823592 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4823593 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem4823592 A P Q). Qed.
Lemma lem4823594 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term267 A c s R) = (term268 A c s R).
Proof. exact (@lem4823593 A (term236 A c s) (term252 A s R)). Qed.
Lemma lem4823595 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term269 A s R x) = (term251 A s R x).
Proof. exact (eq_refl (term269 A s R x)). Qed.
Lemma lem4823596 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term270 A s R) = (term252 A s R).
Proof. exact (fun_ext (fun x : A => @lem4823595 A s R x)). Qed.
Lemma lem4823597 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823598 {A : Type'} (s : A -> Prop) (R : type1402 A) : (term271 A s R) = (term253 A s R).
Proof. exact (MK_COMB (@lem4823597 A) (@lem4823596 A s R)). Qed.
Lemma lem4823599 {A : Type'} (c : type686 A) (s : A -> Prop) : (term237 A c s) = (term237 A c s).
Proof. exact (eq_refl (term237 A c s)). Qed.
Lemma lem4823600 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term267 A c s R) = (term254 A c s R).
Proof. exact (MK_COMB (@lem4823599 A c s) (@lem4823598 A s R)). Qed.
Lemma lem4823601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823602 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term272 A c s R) = (term273 A c s R).
Proof. exact (MK_COMB (@lem4823601) (@lem4823600 A c s R)). Qed.
Lemma lem4823603 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term269 A s R x) = (term251 A s R x).
Proof. exact (eq_refl (term269 A s R x)). Qed.
Lemma lem4823604 {A : Type'} (c : type686 A) (s : A -> Prop) : (term237 A c s) = (term237 A c s).
Proof. exact (eq_refl (term237 A c s)). Qed.
Lemma lem4823605 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term274 A c s R x) = (term275 A c s R x).
Proof. exact (MK_COMB (@lem4823604 A c s) (@lem4823603 A s R x)). Qed.
Lemma lem4823606 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term276 A c s R) = (term277 A c s R).
Proof. exact (fun_ext (fun x : A => @lem4823605 A c s R x)). Qed.
Lemma lem4823607 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823608 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term268 A c s R) = (term278 A c s R).
Proof. exact (MK_COMB (@lem4823607 A) (@lem4823606 A c s R)). Qed.
Lemma lem4823609 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : ((term267 A c s R) = (term268 A c s R)) = ((term254 A c s R) = (term278 A c s R)).
Proof. exact (MK_COMB (@lem4823602 A c s R) (@lem4823608 A c s R)). Qed.
Lemma lem4823610 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term254 A c s R) = (term278 A c s R).
Proof. exact (EQ_MP (@lem4823609 A c s R) (@lem4823594 A c s R)). Qed.
Lemma lem4823612 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4823613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem4823612 A P Q). Qed.
Lemma lem4823614 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term279 A c s R x) = (term280 A c s R x).
Proof. exact (@lem4823613 A (term236 A c s) (term250 A s R x)). Qed.
Lemma lem4823615 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term281 A s R x y) = (term249 A s R x y).
Proof. exact (eq_refl (term281 A s R x y)). Qed.
Lemma lem4823616 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term282 A s R x) = (term250 A s R x).
Proof. exact (fun_ext (fun y : A => @lem4823615 A s R x y)). Qed.
Lemma lem4823617 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823618 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) : (term283 A s R x) = (term251 A s R x).
Proof. exact (MK_COMB (@lem4823617 A) (@lem4823616 A s R x)). Qed.
Lemma lem4823619 {A : Type'} (c : type686 A) (s : A -> Prop) : (term237 A c s) = (term237 A c s).
Proof. exact (eq_refl (term237 A c s)). Qed.
Lemma lem4823620 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term279 A c s R x) = (term275 A c s R x).
Proof. exact (MK_COMB (@lem4823619 A c s) (@lem4823618 A s R x)). Qed.
Lemma lem4823621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823622 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term284 A c s R x) = (term285 A c s R x).
Proof. exact (MK_COMB (@lem4823621) (@lem4823620 A c s R x)). Qed.
Lemma lem4823623 {A : Type'} (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term281 A s R x y) = (term249 A s R x y).
Proof. exact (eq_refl (term281 A s R x y)). Qed.
Lemma lem4823624 {A : Type'} (c : type686 A) (s : A -> Prop) : (term237 A c s) = (term237 A c s).
Proof. exact (eq_refl (term237 A c s)). Qed.
Lemma lem4823625 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term286 A c s R x y) = (term287 A c s R x y).
Proof. exact (MK_COMB (@lem4823624 A c s) (@lem4823623 A s R x y)). Qed.
Lemma lem4823626 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term288 A c s R x) = (term289 A c s R x).
Proof. exact (fun_ext (fun y : A => @lem4823625 A c s R x y)). Qed.
Lemma lem4823627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823628 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term280 A c s R x) = (term290 A c s R x).
Proof. exact (MK_COMB (@lem4823627 A) (@lem4823626 A c s R x)). Qed.
Lemma lem4823629 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : ((term279 A c s R x) = (term280 A c s R x)) = ((term275 A c s R x) = (term290 A c s R x)).
Proof. exact (MK_COMB (@lem4823622 A c s R x) (@lem4823628 A c s R x)). Qed.
Lemma lem4823630 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term275 A c s R x) = (term290 A c s R x).
Proof. exact (EQ_MP (@lem4823629 A c s R x) (@lem4823614 A c s R x)). Qed.
Lemma lem4823631 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term277 A c s R) = (term291 A c s R).
Proof. exact (fun_ext (fun x : A => @lem4823630 A c s R x)). Qed.
Lemma lem4823632 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823633 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term278 A c s R) = (term292 A c s R).
Proof. exact (MK_COMB (@lem4823632 A) (@lem4823631 A c s R)). Qed.
Lemma lem4823634 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term254 A c s R) = (term292 A c s R).
Proof. exact (TRANS (@lem4823610 A c s R) (@lem4823633 A c s R)). Qed.
Lemma lem4823635 {A : Type'} (c : type686 A) (R : type1402 A) : (term255 A c R) = (term293 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823634 A c s R)). Qed.
Lemma lem4823636 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823637 {A : Type'} (c : type686 A) (R : type1402 A) : (term256 A c R) = (term294 A c R).
Proof. exact (MK_COMB (@lem4823636 A) (@lem4823635 A c R)). Qed.
Lemma lem4823662 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) (y : A) : (term287 A c s R x y) = (term287 A c s R x y).
Proof. exact (eq_refl (term287 A c s R x y)). Qed.
Lemma lem4823663 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term289 A c s R x) = (term289 A c s R x).
Proof. exact (fun_ext (fun y : A => @lem4823662 A c s R x y)). Qed.
Lemma lem4823664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823665 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) (x : A) : (term290 A c s R x) = (term290 A c s R x).
Proof. exact (MK_COMB (@lem4823664 A) (@lem4823663 A c s R x)). Qed.
Lemma lem4823666 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term291 A c s R) = (term291 A c s R).
Proof. exact (fun_ext (fun x : A => @lem4823665 A c s R x)). Qed.
Lemma lem4823667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823668 {A : Type'} (c : type686 A) (s : A -> Prop) (R : type1402 A) : (term292 A c s R) = (term292 A c s R).
Proof. exact (MK_COMB (@lem4823667 A) (@lem4823666 A c s R)). Qed.
Lemma lem4823669 {A : Type'} (c : type686 A) (R : type1402 A) : (term293 A c R) = (term293 A c R).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823668 A c s R)). Qed.
Lemma lem4823670 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823671 {A : Type'} (c : type686 A) (R : type1402 A) : (term294 A c R) = (term294 A c R).
Proof. exact (MK_COMB (@lem4823670 A) (@lem4823669 A c R)). Qed.
Lemma lem4823672 {A : Type'} (c : type686 A) (R : type1402 A) : (term256 A c R) = (term294 A c R).
Proof. exact (TRANS (@lem4823637 A c R) (@lem4823671 A c R)). Qed.
Lemma lem4823673 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term294 A c R.
Proof. exact (EQ_MP (@lem4823672 A c R) (@lem4823566 A R c h1)). Qed.
Lemma lem4823675 {A : Type'} (P : A -> Prop) (Q : Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4823676 {A : Type'} (P : A -> Prop) (Q : Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (@lem4823675 A P Q). Qed.
Lemma lem4823677 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term297 A t s) = (term298 A t s).
Proof. exact (@lem4823676 A (term231 A s t) (term232 A t s)). Qed.
Lemma lem4823678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term299 A s t x) = (term230 A s t x).
Proof. exact (eq_refl (term299 A s t x)). Qed.
Lemma lem4823679 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term300 A s t) = (term231 A s t).
Proof. exact (fun_ext (fun x : A => @lem4823678 A s t x)). Qed.
Lemma lem4823680 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823681 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term301 A s t) = (term232 A s t).
Proof. exact (MK_COMB (@lem4823680 A) (@lem4823679 A s t)). Qed.
Lemma lem4823682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823683 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term302 A s t) = (term233 A s t).
Proof. exact (MK_COMB (@lem4823682) (@lem4823681 A s t)). Qed.
Lemma lem4823684 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term232 A t s) = (term232 A t s).
Proof. exact (eq_refl (term232 A t s)). Qed.
Lemma lem4823685 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term297 A t s) = (term234 A t s).
Proof. exact (MK_COMB (@lem4823683 A s t) (@lem4823684 A t s)). Qed.
Lemma lem4823686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823687 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term303 A t s) = (term304 A t s).
Proof. exact (MK_COMB (@lem4823686) (@lem4823685 A t s)). Qed.
Lemma lem4823688 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term299 A s t x) = (term230 A s t x).
Proof. exact (eq_refl (term299 A s t x)). Qed.
Lemma lem4823689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4823690 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term305 A s t x) = (term306 A s t x).
Proof. exact (MK_COMB (@lem4823689) (@lem4823688 A s t x)). Qed.
Lemma lem4823691 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term232 A t s) = (term232 A t s).
Proof. exact (eq_refl (term232 A t s)). Qed.
Lemma lem4823692 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term307 A x t s) = (term308 A x t s).
Proof. exact (MK_COMB (@lem4823690 A s t x) (@lem4823691 A t s)). Qed.
Lemma lem4823693 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term309 A t s) = (term310 A t s).
Proof. exact (fun_ext (fun x : A => @lem4823692 A x t s)). Qed.
Lemma lem4823694 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823695 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term298 A t s) = (term311 A t s).
Proof. exact (MK_COMB (@lem4823694 A) (@lem4823693 A t s)). Qed.
Lemma lem4823696 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term297 A t s) = (term298 A t s)) = ((term234 A t s) = (term311 A t s)).
Proof. exact (MK_COMB (@lem4823687 A t s) (@lem4823695 A t s)). Qed.
Lemma lem4823697 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term234 A t s) = (term311 A t s).
Proof. exact (EQ_MP (@lem4823696 A t s) (@lem4823677 A t s)). Qed.
Lemma lem4823699 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4823700 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem4823699 A P Q). Qed.
Lemma lem4823701 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term312 A x t s) = (term313 A x t s).
Proof. exact (@lem4823700 A (term230 A s t x) (term231 A t s)). Qed.
Lemma lem4823702 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term299 A t s x) = (term230 A t s x).
Proof. exact (eq_refl (term299 A t s x)). Qed.
Lemma lem4823703 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term300 A t s) = (term231 A t s).
Proof. exact (fun_ext (fun x : A => @lem4823702 A t s x)). Qed.
Lemma lem4823704 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823705 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term301 A t s) = (term232 A t s).
Proof. exact (MK_COMB (@lem4823704 A) (@lem4823703 A t s)). Qed.
Lemma lem4823706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term306 A s t x) = (term306 A s t x).
Proof. exact (eq_refl (term306 A s t x)). Qed.
Lemma lem4823707 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term312 A x t s) = (term308 A x t s).
Proof. exact (MK_COMB (@lem4823706 A s t x) (@lem4823705 A t s)). Qed.
Lemma lem4823708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823709 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term314 A x t s) = (term315 A x t s).
Proof. exact (MK_COMB (@lem4823708) (@lem4823707 A x t s)). Qed.
Lemma lem4823710 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term299 A t s x') = (term230 A t s x').
Proof. exact (eq_refl (term299 A t s x')). Qed.
Lemma lem4823711 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term306 A s t x) = (term306 A s t x).
Proof. exact (eq_refl (term306 A s t x)). Qed.
Lemma lem4823712 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term316 A x t s x') = (term317 A x t s x').
Proof. exact (MK_COMB (@lem4823711 A s t x) (@lem4823710 A t s x')). Qed.
Lemma lem4823713 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term318 A x t s) = (term319 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem4823712 A x t s x')). Qed.
Lemma lem4823714 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823715 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term313 A x t s) = (term320 A x t s).
Proof. exact (MK_COMB (@lem4823714 A) (@lem4823713 A x t s)). Qed.
Lemma lem4823716 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term312 A x t s) = (term313 A x t s)) = ((term308 A x t s) = (term320 A x t s)).
Proof. exact (MK_COMB (@lem4823709 A x t s) (@lem4823715 A x t s)). Qed.
Lemma lem4823717 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term308 A x t s) = (term320 A x t s).
Proof. exact (EQ_MP (@lem4823716 A x t s) (@lem4823701 A x t s)). Qed.
Lemma lem4823718 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term310 A t s) = (term321 A t s).
Proof. exact (fun_ext (fun x : A => @lem4823717 A x t s)). Qed.
Lemma lem4823719 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823720 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term311 A t s) = (term322 A t s).
Proof. exact (MK_COMB (@lem4823719 A) (@lem4823718 A t s)). Qed.
Lemma lem4823721 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term234 A t s) = (term322 A t s).
Proof. exact (TRANS (@lem4823697 A t s) (@lem4823720 A t s)). Qed.
Lemma lem4823722 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term239 A s c t) = (term239 A s c t).
Proof. exact (eq_refl (term239 A s c t)). Qed.
Lemma lem4823723 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term240 A c t s) = (term323 A c t s).
Proof. exact (MK_COMB (@lem4823722 A s c t) (@lem4823721 A t s)). Qed.
Lemma lem4823725 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4823726 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem4823725 A P Q). Qed.
Lemma lem4823727 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term324 A c t s) = (term325 A c t s).
Proof. exact (@lem4823726 A (term238 A s c t) (term321 A t s)). Qed.
Lemma lem4823728 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term326 A t s x) = (term320 A x t s).
Proof. exact (eq_refl (term326 A t s x)). Qed.
Lemma lem4823729 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term327 A t s) = (term321 A t s).
Proof. exact (fun_ext (fun x : A => @lem4823728 A x t s)). Qed.
Lemma lem4823730 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823731 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term328 A t s) = (term322 A t s).
Proof. exact (MK_COMB (@lem4823730 A) (@lem4823729 A t s)). Qed.
Lemma lem4823732 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term239 A s c t) = (term239 A s c t).
Proof. exact (eq_refl (term239 A s c t)). Qed.
Lemma lem4823733 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term324 A c t s) = (term323 A c t s).
Proof. exact (MK_COMB (@lem4823732 A s c t) (@lem4823731 A t s)). Qed.
Lemma lem4823734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823735 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term329 A c t s) = (term330 A c t s).
Proof. exact (MK_COMB (@lem4823734) (@lem4823733 A c t s)). Qed.
Lemma lem4823736 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term326 A t s x) = (term320 A x t s).
Proof. exact (eq_refl (term326 A t s x)). Qed.
Lemma lem4823737 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term239 A s c t) = (term239 A s c t).
Proof. exact (eq_refl (term239 A s c t)). Qed.
Lemma lem4823738 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term331 A c t s x) = (term332 A c x t s).
Proof. exact (MK_COMB (@lem4823737 A s c t) (@lem4823736 A x t s)). Qed.
Lemma lem4823739 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term333 A c t s) = (term334 A c t s).
Proof. exact (fun_ext (fun x : A => @lem4823738 A c x t s)). Qed.
Lemma lem4823740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823741 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term325 A c t s) = (term335 A c t s).
Proof. exact (MK_COMB (@lem4823740 A) (@lem4823739 A c t s)). Qed.
Lemma lem4823742 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term324 A c t s) = (term325 A c t s)) = ((term323 A c t s) = (term335 A c t s)).
Proof. exact (MK_COMB (@lem4823735 A c t s) (@lem4823741 A c t s)). Qed.
Lemma lem4823743 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term323 A c t s) = (term335 A c t s).
Proof. exact (EQ_MP (@lem4823742 A c t s) (@lem4823727 A c t s)). Qed.
Lemma lem4823745 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4823746 {A : Type'} (P : Prop) (Q : A -> Prop) : (term265 A P Q) = (term266 A P Q).
Proof. exact (@lem4823745 A P Q). Qed.
Lemma lem4823747 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term336 A c x t s) = (term337 A c x t s).
Proof. exact (@lem4823746 A (term238 A s c t) (term319 A x t s)). Qed.
Lemma lem4823748 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term338 A x t s x') = (term317 A x t s x').
Proof. exact (eq_refl (term338 A x t s x')). Qed.
Lemma lem4823749 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term339 A x t s) = (term319 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem4823748 A x t s x')). Qed.
Lemma lem4823750 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823751 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term340 A x t s) = (term320 A x t s).
Proof. exact (MK_COMB (@lem4823750 A) (@lem4823749 A x t s)). Qed.
Lemma lem4823752 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term239 A s c t) = (term239 A s c t).
Proof. exact (eq_refl (term239 A s c t)). Qed.
Lemma lem4823753 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term336 A c x t s) = (term332 A c x t s).
Proof. exact (MK_COMB (@lem4823752 A s c t) (@lem4823751 A x t s)). Qed.
Lemma lem4823754 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4823755 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term341 A c x t s) = (term342 A c x t s).
Proof. exact (MK_COMB (@lem4823754) (@lem4823753 A c x t s)). Qed.
Lemma lem4823756 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term338 A x t s x') = (term317 A x t s x').
Proof. exact (eq_refl (term338 A x t s x')). Qed.
Lemma lem4823757 {A : Type'} (s : A -> Prop) (c : type686 A) (t : A -> Prop) : (term239 A s c t) = (term239 A s c t).
Proof. exact (eq_refl (term239 A s c t)). Qed.
Lemma lem4823758 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term343 A c x t s x') = (term344 A c x t s x').
Proof. exact (MK_COMB (@lem4823757 A s c t) (@lem4823756 A x t s x')). Qed.
Lemma lem4823759 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term345 A c x t s) = (term346 A c x t s).
Proof. exact (fun_ext (fun x' : A => @lem4823758 A c x t s x')). Qed.
Lemma lem4823760 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823761 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term337 A c x t s) = (term347 A c x t s).
Proof. exact (MK_COMB (@lem4823760 A) (@lem4823759 A c x t s)). Qed.
Lemma lem4823762 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : ((term336 A c x t s) = (term337 A c x t s)) = ((term332 A c x t s) = (term347 A c x t s)).
Proof. exact (MK_COMB (@lem4823755 A c x t s) (@lem4823761 A c x t s)). Qed.
Lemma lem4823763 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term332 A c x t s) = (term347 A c x t s).
Proof. exact (EQ_MP (@lem4823762 A c x t s) (@lem4823747 A c x t s)). Qed.
Lemma lem4823764 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term334 A c t s) = (term348 A c t s).
Proof. exact (fun_ext (fun x : A => @lem4823763 A c x t s)). Qed.
Lemma lem4823765 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823766 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term335 A c t s) = (term349 A c t s).
Proof. exact (MK_COMB (@lem4823765 A) (@lem4823764 A c t s)). Qed.
Lemma lem4823767 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term323 A c t s) = (term349 A c t s).
Proof. exact (TRANS (@lem4823743 A c t s) (@lem4823766 A c t s)). Qed.
Lemma lem4823768 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term240 A c t s) = (term349 A c t s).
Proof. exact (TRANS (@lem4823723 A c t s) (@lem4823767 A c t s)). Qed.
Lemma lem4823769 {A : Type'} (c : type686 A) (s : A -> Prop) : (term241 A c s) = (term350 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823768 A c t s)). Qed.
Lemma lem4823770 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823771 {A : Type'} (c : type686 A) (s : A -> Prop) : (term242 A c s) = (term351 A c s).
Proof. exact (MK_COMB (@lem4823770 A) (@lem4823769 A c s)). Qed.
Lemma lem4823772 {A : Type'} (c : type686 A) : (term243 A c) = (term352 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823771 A c s)). Qed.
Lemma lem4823773 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823774 {A : Type'} (c : type686 A) : (term244 A c) = (term353 A c).
Proof. exact (MK_COMB (@lem4823773 A) (@lem4823772 A c)). Qed.
Lemma lem4823805 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term344 A c x t s x') = (term344 A c x t s x').
Proof. exact (eq_refl (term344 A c x t s x')). Qed.
Lemma lem4823806 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term346 A c x t s) = (term346 A c x t s).
Proof. exact (fun_ext (fun x' : A => @lem4823805 A c x t s x')). Qed.
Lemma lem4823807 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823808 {A : Type'} (c : type686 A) (x : A) (t : A -> Prop) (s : A -> Prop) : (term347 A c x t s) = (term347 A c x t s).
Proof. exact (MK_COMB (@lem4823807 A) (@lem4823806 A c x t s)). Qed.
Lemma lem4823809 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term348 A c t s) = (term348 A c t s).
Proof. exact (fun_ext (fun x : A => @lem4823808 A c x t s)). Qed.
Lemma lem4823810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4823811 {A : Type'} (c : type686 A) (t : A -> Prop) (s : A -> Prop) : (term349 A c t s) = (term349 A c t s).
Proof. exact (MK_COMB (@lem4823810 A) (@lem4823809 A c t s)). Qed.
Lemma lem4823812 {A : Type'} (c : type686 A) (s : A -> Prop) : (term350 A c s) = (term350 A c s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4823811 A c t s)). Qed.
Lemma lem4823813 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823814 {A : Type'} (c : type686 A) (s : A -> Prop) : (term351 A c s) = (term351 A c s).
Proof. exact (MK_COMB (@lem4823813 A) (@lem4823812 A c s)). Qed.
Lemma lem4823815 {A : Type'} (c : type686 A) : (term352 A c) = (term352 A c).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4823814 A c s)). Qed.
Lemma lem4823816 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4823817 {A : Type'} (c : type686 A) : (term353 A c) = (term353 A c).
Proof. exact (MK_COMB (@lem4823816 A) (@lem4823815 A c)). Qed.
Lemma lem4823818 {A : Type'} (c : type686 A) : (term244 A c) = (term353 A c).
Proof. exact (TRANS (@lem4823774 A c) (@lem4823817 A c)). Qed.
Lemma lem4823819 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term353 A c.
Proof. exact (EQ_MP (@lem4823818 A c) (@lem4823565 A R c h1)). Qed.
Lemma lem4823820 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term354 A c R _59796.
Proof. exact (@lem4823673 A R c h1 _59796). Qed.
Lemma lem4823821 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) : (term354 A c R _59796) = (term292 A c _59796 R).
Proof. exact (eq_refl (term354 A c R _59796)). Qed.
Lemma lem4823822 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term292 A c _59796 R.
Proof. exact (EQ_MP (@lem4823821 A c _59796 R) (@lem4823820 A _59796 R c h1)). Qed.
Lemma lem4823823 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term355 A c _59796 R _59797.
Proof. exact (@lem4823822 A _59796 R c h1 _59797). Qed.
Lemma lem4823824 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) : (term355 A c _59796 R _59797) = (term290 A c _59796 R _59797).
Proof. exact (eq_refl (term355 A c _59796 R _59797)). Qed.
Lemma lem4823825 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term290 A c _59796 R _59797.
Proof. exact (EQ_MP (@lem4823824 A c _59796 R _59797) (@lem4823823 A _59796 _59797 R c h1)). Qed.
Lemma lem4823826 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term356 A c _59796 R _59797 _59798.
Proof. exact (@lem4823825 A _59796 _59797 R c h1 _59798). Qed.
Lemma lem4823827 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term356 A c _59796 R _59797 _59798) = (term287 A c _59796 R _59797 _59798).
Proof. exact (eq_refl (term356 A c _59796 R _59797 _59798)). Qed.
Lemma lem4823828 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term287 A c _59796 R _59797 _59798.
Proof. exact (EQ_MP (@lem4823827 A c _59796 R _59797 _59798) (@lem4823826 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4823829 {A : Type'} (_59799 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term357 A c _59799.
Proof. exact (@lem4823819 A R c h1 _59799). Qed.
Lemma lem4823830 {A : Type'} (c : type686 A) (_59799 : A -> Prop) : (term357 A c _59799) = (term351 A c _59799).
Proof. exact (eq_refl (term357 A c _59799)). Qed.
Lemma lem4823831 {A : Type'} (_59799 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term351 A c _59799.
Proof. exact (EQ_MP (@lem4823830 A c _59799) (@lem4823829 A _59799 R c h1)). Qed.
Lemma lem4823832 {A : Type'} (_59799 : A -> Prop) (_59800 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term358 A c _59799 _59800.
Proof. exact (@lem4823831 A _59799 R c h1 _59800). Qed.
Lemma lem4823833 {A : Type'} (c : type686 A) (_59800 : A -> Prop) (_59799 : A -> Prop) : (term358 A c _59799 _59800) = (term349 A c _59800 _59799).
Proof. exact (eq_refl (term358 A c _59799 _59800)). Qed.
Lemma lem4823834 {A : Type'} (_59800 : A -> Prop) (_59799 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term349 A c _59800 _59799.
Proof. exact (EQ_MP (@lem4823833 A c _59800 _59799) (@lem4823832 A _59799 _59800 R c h1)). Qed.
Lemma lem4823835 {A : Type'} (_59800 : A -> Prop) (_59799 : A -> Prop) (_59801 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term359 A c _59800 _59799 _59801.
Proof. exact (@lem4823834 A _59800 _59799 R c h1 _59801). Qed.
Lemma lem4823836 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) : (term359 A c _59800 _59799 _59801) = (term347 A c _59801 _59800 _59799).
Proof. exact (eq_refl (term359 A c _59800 _59799 _59801)). Qed.
Lemma lem4823837 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term347 A c _59801 _59800 _59799.
Proof. exact (EQ_MP (@lem4823836 A c _59801 _59800 _59799) (@lem4823835 A _59800 _59799 _59801 R c h1)). Qed.
Lemma lem4823838 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term360 A c _59801 _59800 _59799 _59802.
Proof. exact (@lem4823837 A _59801 _59800 _59799 R c h1 _59802). Qed.
Lemma lem4823839 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term360 A c _59801 _59800 _59799 _59802) = (term344 A c _59801 _59800 _59799 _59802).
Proof. exact (eq_refl (term360 A c _59801 _59800 _59799 _59802)). Qed.
Lemma lem4823840 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term344 A c _59801 _59800 _59799 _59802.
Proof. exact (EQ_MP (@lem4823839 A c _59801 _59800 _59799 _59802) (@lem4823838 A _59801 _59800 _59799 _59802 R c h1)). Qed.
Lemma lem4823844 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term62 A x y.
Proof. exact (proj2 (@lem4823557 A t c t' x y h1)). Qed.
Lemma lem4823856 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term249 A _59796 R _59797 _59798) = (term361 A _59796 R _59797 _59798).
Proof. exact (@lem4821888 (term228 A _59796 _59797) (term246 A _59796 _59797 _59798) (term245 A R _59797 _59798)). Qed.
Lemma lem4823863 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term362 A _59796 R _59797 _59798) = (term363 A _59796 R _59797 _59798).
Proof. exact (@lem4821888 (term228 A _59796 _59798) (_59797 = _59798) (term245 A R _59797 _59798)). Qed.
Lemma lem4823864 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term229 A _59796 _59797) = (term229 A _59796 _59797).
Proof. exact (eq_refl (term229 A _59796 _59797)). Qed.
Lemma lem4823867 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term361 A _59796 R _59797 _59798) = (term364 A _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4823864 A _59796 _59797) (@lem4823863 A _59796 R _59797 _59798)). Qed.
Lemma lem4823869 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term249 A _59796 R _59797 _59798) = (term364 A _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4823856 A _59796 R _59797 _59798) (@lem4823867 A _59796 R _59797 _59798)). Qed.
Lemma lem4823870 {A : Type'} (c : type686 A) (_59796 : A -> Prop) : (term237 A c _59796) = (term237 A c _59796).
Proof. exact (eq_refl (term237 A c _59796)). Qed.
Lemma lem4823873 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term287 A c _59796 R _59797 _59798) = (term365 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4823870 A c _59796) (@lem4823869 A _59796 R _59797 _59798)). Qed.
Lemma lem4823874 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term365 A c _59796 R _59797 _59798.
Proof. exact (EQ_MP (@lem4823873 A c _59796 R _59797 _59798) (@lem4823828 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4823889 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term317 A _59801 _59800 _59799 _59802) = (term366 A _59801 _59800 _59799 _59802).
Proof. exact (@lem4821888 (term228 A _59799 _59801) (@I (A -> Prop) _59800 _59801) (term230 A _59800 _59799 _59802)). Qed.
Lemma lem4823890 {A : Type'} (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term239 A _59799 c _59800) = (term239 A _59799 c _59800).
Proof. exact (eq_refl (term239 A _59799 c _59800)). Qed.
Lemma lem4823891 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term344 A c _59801 _59800 _59799 _59802) = (term367 A c _59801 _59800 _59799 _59802).
Proof. exact (MK_COMB (@lem4823890 A _59799 c _59800) (@lem4823889 A _59801 _59800 _59799 _59802)). Qed.
Lemma lem4823898 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term367 A c _59801 _59800 _59799 _59802) = (term368 A c _59801 _59800 _59799 _59802).
Proof. exact (@lem4821888 (term236 A c _59799) (term236 A c _59800) (term366 A _59801 _59800 _59799 _59802)). Qed.
Lemma lem4823899 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term344 A c _59801 _59800 _59799 _59802) = (term368 A c _59801 _59800 _59799 _59802).
Proof. exact (TRANS (@lem4823891 A c _59801 _59800 _59799 _59802) (@lem4823898 A c _59801 _59800 _59799 _59802)). Qed.
Lemma lem4823900 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term368 A c _59801 _59800 _59799 _59802.
Proof. exact (EQ_MP (@lem4823899 A c _59801 _59800 _59799 _59802) (@lem4823840 A _59801 _59800 _59799 _59802 R c h1)). Qed.
Lemma lem4823963 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t.
Proof. exact (proj1 (@lem4823558 A t c t' x y h1)). Qed.
Lemma lem4823964 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term369 A c t.
Proof. exact (fun h0 : term236 A c t => @lem4823963 A t c t' x y h1). Qed.
Lemma lem4823966 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4823967 {A : Type'} (c : type686 A) (t : A -> Prop) : (term369 A c t) = (@I ((A -> Prop) -> Prop) c t).
Proof. exact (@lem4823966 (@I ((A -> Prop) -> Prop) c t)). Qed.
Lemma lem4823968 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t.
Proof. exact (EQ_MP (@lem4823967 A c t) (@lem4823964 A t c t' x y h1)). Qed.
Lemma lem4823970 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4823558 A t c t' x y h1)). Qed.
Lemma lem4823971 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term371 A t x.
Proof. exact (fun h0 : term228 A t x => @lem4823970 A t c t' x y h1). Qed.
Lemma lem4823973 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4823974 {A : Type'} (t : A -> Prop) (x : A) : (term371 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4823973 (@I (A -> Prop) t x)). Qed.
Lemma lem4823975 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4823974 A t x) (@lem4823971 A t c t' x y h1)). Qed.
Lemma lem4823977 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t.
Proof. exact (proj1 (@lem4823558 A t c t' x y h1)). Qed.
Lemma lem4823978 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term369 A c t.
Proof. exact (fun h0 : term236 A c t => @lem4823977 A t c t' x y h1). Qed.
Lemma lem4823980 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4823981 {A : Type'} (c : type686 A) (t : A -> Prop) : (term369 A c t) = (@I ((A -> Prop) -> Prop) c t).
Proof. exact (@lem4823980 (@I ((A -> Prop) -> Prop) c t)). Qed.
Lemma lem4823982 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t.
Proof. exact (EQ_MP (@lem4823981 A c t) (@lem4823978 A t c t' x y h1)). Qed.
Lemma lem4823984 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t'.
Proof. exact (proj1 (@lem4823560 A t c t' x y h1)). Qed.
Lemma lem4823985 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term369 A c t'.
Proof. exact (fun h0 : term236 A c t' => @lem4823984 A t c t' x y h1). Qed.
Lemma lem4823987 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4823988 {A : Type'} (c : type686 A) (t' : A -> Prop) : (term369 A c t') = (@I ((A -> Prop) -> Prop) c t').
Proof. exact (@lem4823987 (@I ((A -> Prop) -> Prop) c t')). Qed.
Lemma lem4823989 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t'.
Proof. exact (EQ_MP (@lem4823988 A c t') (@lem4823985 A t c t' x y h1)). Qed.
Lemma lem4823991 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4823558 A t c t' x y h1)). Qed.
Lemma lem4823992 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term371 A t x.
Proof. exact (fun h0 : term228 A t x => @lem4823991 A t c t' x y h1). Qed.
Lemma lem4823994 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4823995 {A : Type'} (t : A -> Prop) (x : A) : (term371 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4823994 (@I (A -> Prop) t x)). Qed.
Lemma lem4823996 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4823995 A t x) (@lem4823992 A t c t' x y h1)). Qed.
Lemma lem4823998 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t'.
Proof. exact (proj1 (@lem4823560 A t c t' x y h1)). Qed.
Lemma lem4823999 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term369 A c t'.
Proof. exact (fun h0 : term236 A c t' => @lem4823998 A t c t' x y h1). Qed.
Lemma lem4824001 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4824002 {A : Type'} (c : type686 A) (t' : A -> Prop) : (term369 A c t') = (@I ((A -> Prop) -> Prop) c t').
Proof. exact (@lem4824001 (@I ((A -> Prop) -> Prop) c t')). Qed.
Lemma lem4824003 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I ((A -> Prop) -> Prop) c t'.
Proof. exact (EQ_MP (@lem4824002 A c t') (@lem4823999 A t c t' x y h1)). Qed.
Lemma lem4824005 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t' y.
Proof. exact (proj2 (@lem4823560 A t c t' x y h1)). Qed.
Lemma lem4824006 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term371 A t' y.
Proof. exact (fun h0 : term228 A t' y => @lem4824005 A t c t' x y h1). Qed.
Lemma lem4824008 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4824009 {A : Type'} (t' : A -> Prop) (y : A) : (term371 A t' y) = (@I (A -> Prop) t' y).
Proof. exact (@lem4824008 (@I (A -> Prop) t' y)). Qed.
Lemma lem4824010 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t' y.
Proof. exact (EQ_MP (@lem4824009 A t' y) (@lem4824006 A t c t' x y h1)). Qed.
Lemma lem4824013 {A : Type'} (x : A) (y : A) (h1 : term62 A x y) : term62 A x y.
Proof. exact (h1). Qed.
Lemma lem4824014 {A : Type'} (x : A) (y : A) (h1 : term62 A x y) : term372 A x y.
Proof. exact (fun h0 : x = y => @lem4824013 A x y h1). Qed.
Lemma lem4824016 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4824017 {A : Type'} (x : A) (y : A) : (term372 A x y) = (term62 A x y).
Proof. exact (@lem4824016 (x = y)). Qed.
Lemma lem4824018 {A : Type'} (x : A) (y : A) (h1 : term62 A x y) : term62 A x y.
Proof. exact (EQ_MP (@lem4824017 A x y) (@lem4824014 A x y h1)). Qed.
Lemma lem4824020 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term259 A R x y.
Proof. exact (EQ_MP (@lem4823503 A R x y) (@lem4823322 A R x y h1)). Qed.
Lemma lem4824021 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term374 A R x y.
Proof. exact (fun h0 : term245 A R x y => @lem4824020 A R x y h1). Qed.
Lemma lem4824023 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4824024 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term374 A R x y) = (term259 A R x y).
Proof. exact (@lem4824023 (term245 A R x y)). Qed.
Lemma lem4824025 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term259 A R x y.
Proof. exact (EQ_MP (@lem4824024 A R x y) (@lem4824021 A R x y h1)). Qed.
Lemma lem4824031 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824032 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798).
Proof. exact (@lem4824031 (term228 A _59796 _59797) (term236 A c _59796) (term363 A _59796 R _59797 _59798)). Qed.
Lemma lem4824046 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824047 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term376 A c _59796 R _59797 _59798) = (term377 A c _59796 R _59797 _59798).
Proof. exact (@lem4824046 (term228 A _59796 _59798) (term236 A c _59796) (term378 A R _59797 _59798)). Qed.
Lemma lem4824061 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824062 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term379 A c _59796 R _59797 _59798) = (term380 A c _59796 R _59797 _59798).
Proof. exact (@lem4824061 (_59797 = _59798) (term236 A c _59796) (term245 A R _59797 _59798)). Qed.
Lemma lem4824078 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4824079 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term381 A c _59796 R _59797 _59798) = (term382 A R _59797 _59798 c _59796).
Proof. exact (@lem4824078 (term245 A R _59797 _59798) (term236 A c _59796)). Qed.
Lemma lem4824085 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824086 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term380 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824085 A _59797 _59798) (@lem4824079 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824097 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term379 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824062 A c _59796 R _59797 _59798) (@lem4824086 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824098 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term229 A _59796 _59798) = (term229 A _59796 _59798).
Proof. exact (eq_refl (term229 A _59796 _59798)). Qed.
Lemma lem4824099 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term385 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824098 A _59796 _59798) (@lem4824097 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824103 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824104 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term386 A R _59797 _59798 c _59796).
Proof. exact (@lem4824103 (_59797 = _59798) (term228 A _59796 _59798) (term382 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824120 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824121 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term387 A R _59797 _59798 c _59796) = (term388 A R _59797 _59798 c _59796).
Proof. exact (@lem4824120 (term245 A R _59797 _59798) (term228 A _59796 _59798) (term236 A c _59796)). Qed.
Lemma lem4824137 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824138 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term386 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824137 A _59797 _59798) (@lem4824121 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824149 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824104 A R _59797 _59798 c _59796) (@lem4824138 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824150 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824099 A R _59797 _59798 c _59796) (@lem4824149 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824151 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term376 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824047 A c _59796 R _59797 _59798) (@lem4824150 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824152 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term229 A _59796 _59797) = (term229 A _59796 _59797).
Proof. exact (eq_refl (term229 A _59796 _59797)). Qed.
Lemma lem4824153 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term390 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824152 A _59796 _59797) (@lem4824151 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824157 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824158 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term391 A R _59797 _59798 c _59796).
Proof. exact (@lem4824157 (_59797 = _59798) (term228 A _59796 _59797) (term388 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824174 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824175 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term392 A R _59797 _59798 c _59796) = (term393 A R _59797 _59798 c _59796).
Proof. exact (@lem4824174 (term245 A R _59797 _59798) (term228 A _59796 _59797) (term394 A _59798 c _59796)). Qed.
Lemma lem4824201 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824202 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term391 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824201 A _59797 _59798) (@lem4824175 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824213 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824158 A R _59797 _59798 c _59796) (@lem4824202 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824214 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824153 A R _59797 _59798 c _59796) (@lem4824213 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824215 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term365 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824032 A c _59796 R _59797 _59798) (@lem4824214 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4824217 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term396 A c _59796 R _59797 _59798) = (term397 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824216) (@lem4824215 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824232 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term376 A c _59796 R _59797 _59798) = (term377 A c _59796 R _59797 _59798).
Proof. exact (@lem4824231 (term228 A _59796 _59798) (term236 A c _59796) (term378 A R _59797 _59798)). Qed.
Lemma lem4824246 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824247 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term379 A c _59796 R _59797 _59798) = (term380 A c _59796 R _59797 _59798).
Proof. exact (@lem4824246 (_59797 = _59798) (term236 A c _59796) (term245 A R _59797 _59798)). Qed.
Lemma lem4824263 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4824264 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term381 A c _59796 R _59797 _59798) = (term382 A R _59797 _59798 c _59796).
Proof. exact (@lem4824263 (term245 A R _59797 _59798) (term236 A c _59796)). Qed.
Lemma lem4824270 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824271 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term380 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824270 A _59797 _59798) (@lem4824264 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824282 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term379 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824247 A c _59796 R _59797 _59798) (@lem4824271 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824283 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term229 A _59796 _59798) = (term229 A _59796 _59798).
Proof. exact (eq_refl (term229 A _59796 _59798)). Qed.
Lemma lem4824284 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term385 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824283 A _59796 _59798) (@lem4824282 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824288 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824289 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term386 A R _59797 _59798 c _59796).
Proof. exact (@lem4824288 (_59797 = _59798) (term228 A _59796 _59798) (term382 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824305 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824306 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term387 A R _59797 _59798 c _59796) = (term388 A R _59797 _59798 c _59796).
Proof. exact (@lem4824305 (term245 A R _59797 _59798) (term228 A _59796 _59798) (term236 A c _59796)). Qed.
Lemma lem4824322 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824323 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term386 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824322 A _59797 _59798) (@lem4824306 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824334 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824289 A R _59797 _59798 c _59796) (@lem4824323 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824335 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824284 A R _59797 _59798 c _59796) (@lem4824334 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824336 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term376 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824232 A c _59796 R _59797 _59798) (@lem4824335 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824337 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term229 A _59796 _59797) = (term229 A _59796 _59797).
Proof. exact (eq_refl (term229 A _59796 _59797)). Qed.
Lemma lem4824338 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term390 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824337 A _59796 _59797) (@lem4824336 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824342 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824343 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term391 A R _59797 _59798 c _59796).
Proof. exact (@lem4824342 (_59797 = _59798) (term228 A _59796 _59797) (term388 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824359 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824360 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term392 A R _59797 _59798 c _59796) = (term393 A R _59797 _59798 c _59796).
Proof. exact (@lem4824359 (term245 A R _59797 _59798) (term228 A _59796 _59797) (term394 A _59798 c _59796)). Qed.
Lemma lem4824386 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4824387 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term391 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4824386 A _59797 _59798) (@lem4824360 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824398 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824343 A R _59797 _59798 c _59796) (@lem4824387 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824399 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4824338 A R _59797 _59798 c _59796) (@lem4824398 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824400 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : ((term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798)) = ((term395 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796)).
Proof. exact (MK_COMB (@lem4824217 A R _59797 _59798 c _59796) (@lem4824399 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824402 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4824403 (x : Prop) : (x = x) = True.
Proof. exact (@lem4824402 Prop x). Qed.
Lemma lem4824404 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : ((term395 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796)) = True.
Proof. exact (@lem4824403 (term395 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824405 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : ((term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798)) = True.
Proof. exact (TRANS (@lem4824400 A R _59797 _59798 c _59796) (@lem4824404 A R _59797 _59798 c _59796)). Qed.
Lemma lem4824406 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : True = ((term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798)).
Proof. exact (SYM (@lem4824405 A c _59796 R _59797 _59798)). Qed.
Lemma lem4824407 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798).
Proof. exact (EQ_MP (@lem4824406 A c _59796 R _59797 _59798) (@lem0)). Qed.
Lemma lem4824408 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term375 A c _59796 R _59797 _59798.
Proof. exact (EQ_MP (@lem4824407 A c _59796 R _59797 _59798) (@lem4823874 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4824410 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4824411 {A : Type'} (c : type686 A) (R : type1402 A) (_59798 : A) (_59796 : A -> Prop) (_59797 : A) : (term375 A c _59796 R _59797 _59798) = (term399 A c R _59798 _59796 _59797).
Proof. exact (@lem4824410 (term376 A c _59796 R _59797 _59798) (term228 A _59796 _59797)). Qed.
Lemma lem4824413 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824414 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term402 A c _59796 R _59797 _59798) = (term403 A c _59796 R _59797 _59798).
Proof. exact (@lem4824413 (term236 A c _59796) (term363 A _59796 R _59797 _59798)). Qed.
Lemma lem4824416 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824417 {A : Type'} (c : type686 A) (_59796 : A -> Prop) : (term404 A c _59796) = (@I ((A -> Prop) -> Prop) c _59796).
Proof. exact (@lem4824416 (@I ((A -> Prop) -> Prop) c _59796)). Qed.
Lemma lem4824418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4824419 {A : Type'} (c : type686 A) (_59796 : A -> Prop) : (term405 A c _59796) = (term260 A c _59796).
Proof. exact (MK_COMB (@lem4824418) (@lem4824417 A c _59796)). Qed.
Lemma lem4824421 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824422 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term406 A _59796 R _59797 _59798) = (term407 A _59796 R _59797 _59798).
Proof. exact (@lem4824421 (term228 A _59796 _59798) (term378 A R _59797 _59798)). Qed.
Lemma lem4824424 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824425 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term408 A _59796 _59798) = (@I (A -> Prop) _59796 _59798).
Proof. exact (@lem4824424 (@I (A -> Prop) _59796 _59798)). Qed.
Lemma lem4824426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4824427 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term409 A _59796 _59798) = (term410 A _59796 _59798).
Proof. exact (MK_COMB (@lem4824426) (@lem4824425 A _59796 _59798)). Qed.
Lemma lem4824429 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824430 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) : (term411 A R _59797 _59798) = (term412 A R _59797 _59798).
Proof. exact (@lem4824429 (_59797 = _59798) (term245 A R _59797 _59798)). Qed.
Lemma lem4824431 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term407 A _59796 R _59797 _59798) = (term413 A _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4824427 A _59796 _59798) (@lem4824430 A R _59797 _59798)). Qed.
Lemma lem4824432 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term406 A _59796 R _59797 _59798) = (term413 A _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4824422 A _59796 R _59797 _59798) (@lem4824431 A _59796 R _59797 _59798)). Qed.
Lemma lem4824433 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term403 A c _59796 R _59797 _59798) = (term414 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4824419 A c _59796) (@lem4824432 A _59796 R _59797 _59798)). Qed.
Lemma lem4824434 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term402 A c _59796 R _59797 _59798) = (term414 A c _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4824414 A c _59796 R _59797 _59798) (@lem4824433 A c _59796 R _59797 _59798)). Qed.
Lemma lem4824435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4824436 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term415 A c _59796 R _59797 _59798) = (term416 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4824435) (@lem4824434 A c _59796 R _59797 _59798)). Qed.
Lemma lem4824437 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term228 A _59796 _59797) = (term228 A _59796 _59797).
Proof. exact (eq_refl (term228 A _59796 _59797)). Qed.
Lemma lem4824438 {A : Type'} (c : type686 A) (R : type1402 A) (_59798 : A) (_59796 : A -> Prop) (_59797 : A) : (term399 A c R _59798 _59796 _59797) = (term417 A c R _59798 _59796 _59797).
Proof. exact (MK_COMB (@lem4824436 A c _59796 R _59797 _59798) (@lem4824437 A _59796 _59797)). Qed.
Lemma lem4824439 {A : Type'} (c : type686 A) (R : type1402 A) (_59798 : A) (_59796 : A -> Prop) (_59797 : A) : (term375 A c _59796 R _59797 _59798) = (term417 A c R _59798 _59796 _59797).
Proof. exact (TRANS (@lem4824411 A c R _59798 _59796 _59797) (@lem4824438 A c R _59798 _59796 _59797)). Qed.
Lemma lem4824441 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) : term412 A R x y.
Proof. exact (conj (@lem4824018 A x y h1) (@lem4824025 A R x y h2)). Qed.
Lemma lem4824442 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term221 A t c t' x y) : term413 A t' R x y.
Proof. exact (conj (@lem4824010 A t c t' x y h3) (@lem4824441 A R x y h1 h2)). Qed.
Lemma lem4824443 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term221 A t c t' x y) : term414 A c t' R x y.
Proof. exact (conj (@lem4824003 A t c t' x y h3) (@lem4824442 A R t c t' x y h1 h2 h3)). Qed.
Lemma lem4824445 {A : Type'} (_59798 : A) (_59796 : A -> Prop) (_59797 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term417 A c R _59798 _59796 _59797.
Proof. exact (EQ_MP (@lem4824439 A c R _59798 _59796 _59797) (@lem4824408 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4824446 {A : Type'} (_59798 : A) (_59796 : A -> Prop) (_59797 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term417 A c R _59798 _59796 _59797.
Proof. exact (@lem4824445 A _59798 _59796 _59797 R c h1). Qed.
Lemma lem4824447 {A : Type'} (y : A) (t' : A -> Prop) (x : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term417 A c R y t' x.
Proof. exact (@lem4824446 A y t' x R c h1). Qed.
Lemma lem4824450 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term228 A t' x.
Proof. exact (@lem4824447 A y t' x R c h3 (@lem4824443 A R t c t' x y h1 h2 h4)). Qed.
Lemma lem4824451 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term418 A t' x.
Proof. exact (fun h0 : @I (A -> Prop) t' x => @lem4824450 A R t c t' x y h1 h2 h3 h4). Qed.
Lemma lem4824453 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4824454 {A : Type'} (t' : A -> Prop) (x : A) : (term418 A t' x) = (term228 A t' x).
Proof. exact (@lem4824453 (@I (A -> Prop) t' x)). Qed.
Lemma lem4824455 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term228 A t' x.
Proof. exact (EQ_MP (@lem4824454 A t' x) (@lem4824451 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4824457 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t' y.
Proof. exact (proj2 (@lem4823560 A t c t' x y h1)). Qed.
Lemma lem4824458 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term371 A t' y.
Proof. exact (fun h0 : term228 A t' y => @lem4824457 A t c t' x y h1). Qed.
Lemma lem4824460 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4824461 {A : Type'} (t' : A -> Prop) (y : A) : (term371 A t' y) = (@I (A -> Prop) t' y).
Proof. exact (@lem4824460 (@I (A -> Prop) t' y)). Qed.
Lemma lem4824462 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : @I (A -> Prop) t' y.
Proof. exact (EQ_MP (@lem4824461 A t' y) (@lem4824458 A t c t' x y h1)). Qed.
Lemma lem4824478 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824479 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term419 A c _59801 _59800 _59799 _59802) = (term420 A c _59801 _59800 _59799 _59802).
Proof. exact (@lem4824478 (term228 A _59799 _59801) (term236 A c _59800) (term421 A _59801 _59800 _59799 _59802)). Qed.
Lemma lem4824493 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824494 {A : Type'} (_59801 : A) (c : type686 A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term422 A c _59801 _59800 _59799 _59802) = (term423 A _59801 c _59800 _59799 _59802).
Proof. exact (@lem4824493 (@I (A -> Prop) _59800 _59801) (term236 A c _59800) (term230 A _59800 _59799 _59802)). Qed.
Lemma lem4824508 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824509 {A : Type'} (c : type686 A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term424 A c _59800 _59799 _59802) = (term425 A c _59800 _59799 _59802).
Proof. exact (@lem4824508 (term228 A _59800 _59802) (term236 A c _59800) (@I (A -> Prop) _59799 _59802)). Qed.
Lemma lem4824523 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4824524 {A : Type'} (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term426 A c _59800 _59799 _59802) = (term427 A _59799 _59802 c _59800).
Proof. exact (@lem4824523 (@I (A -> Prop) _59799 _59802) (term236 A c _59800)). Qed.
Lemma lem4824530 {A : Type'} (_59800 : A -> Prop) (_59802 : A) : (term229 A _59800 _59802) = (term229 A _59800 _59802).
Proof. exact (eq_refl (term229 A _59800 _59802)). Qed.
Lemma lem4824531 {A : Type'} (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term425 A c _59800 _59799 _59802) = (term428 A _59799 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824530 A _59800 _59802) (@lem4824524 A _59799 _59802 c _59800)). Qed.
Lemma lem4824535 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824536 {A : Type'} (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term428 A _59799 _59802 c _59800) = (term429 A _59799 _59802 c _59800).
Proof. exact (@lem4824535 (@I (A -> Prop) _59799 _59802) (term228 A _59800 _59802) (term236 A c _59800)). Qed.
Lemma lem4824552 {A : Type'} (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term425 A c _59800 _59799 _59802) = (term429 A _59799 _59802 c _59800).
Proof. exact (TRANS (@lem4824531 A _59799 _59802 c _59800) (@lem4824536 A _59799 _59802 c _59800)). Qed.
Lemma lem4824553 {A : Type'} (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term424 A c _59800 _59799 _59802) = (term429 A _59799 _59802 c _59800).
Proof. exact (TRANS (@lem4824509 A c _59800 _59799 _59802) (@lem4824552 A _59799 _59802 c _59800)). Qed.
Lemma lem4824554 {A : Type'} (_59800 : A -> Prop) (_59801 : A) : (term430 A _59800 _59801) = (term430 A _59800 _59801).
Proof. exact (eq_refl (term430 A _59800 _59801)). Qed.
Lemma lem4824555 {A : Type'} (_59801 : A) (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term423 A _59801 c _59800 _59799 _59802) = (term431 A _59801 _59799 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824554 A _59800 _59801) (@lem4824553 A _59799 _59802 c _59800)). Qed.
Lemma lem4824559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824560 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term431 A _59801 _59799 _59802 c _59800) = (term432 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824559 (@I (A -> Prop) _59799 _59802) (@I (A -> Prop) _59800 _59801) (term394 A _59802 c _59800)). Qed.
Lemma lem4824586 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term423 A _59801 c _59800 _59799 _59802) = (term432 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824555 A _59801 _59799 _59802 c _59800) (@lem4824560 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824587 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term422 A c _59801 _59800 _59799 _59802) = (term432 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824494 A _59801 c _59800 _59799 _59802) (@lem4824586 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824588 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term229 A _59799 _59801) = (term229 A _59799 _59801).
Proof. exact (eq_refl (term229 A _59799 _59801)). Qed.
Lemma lem4824589 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term420 A c _59801 _59800 _59799 _59802) = (term433 A _59799 _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824588 A _59799 _59801) (@lem4824587 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824593 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824594 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term433 A _59799 _59801 _59802 c _59800) = (term434 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824593 (@I (A -> Prop) _59799 _59802) (term228 A _59799 _59801) (term435 A _59801 _59802 c _59800)). Qed.
Lemma lem4824608 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824609 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term436 A _59799 _59801 _59802 c _59800) = (term437 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824608 (@I (A -> Prop) _59800 _59801) (term228 A _59799 _59801) (term394 A _59802 c _59800)). Qed.
Lemma lem4824635 {A : Type'} (_59799 : A -> Prop) (_59802 : A) : (term430 A _59799 _59802) = (term430 A _59799 _59802).
Proof. exact (eq_refl (term430 A _59799 _59802)). Qed.
Lemma lem4824636 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term434 A _59799 _59801 _59802 c _59800) = (term438 A _59799 _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824635 A _59799 _59802) (@lem4824609 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824647 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term433 A _59799 _59801 _59802 c _59800) = (term438 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824594 A _59799 _59801 _59802 c _59800) (@lem4824636 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824648 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term420 A c _59801 _59800 _59799 _59802) = (term438 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824589 A _59799 _59801 _59802 c _59800) (@lem4824647 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824649 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term419 A c _59801 _59800 _59799 _59802) = (term438 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824479 A c _59801 _59800 _59799 _59802) (@lem4824648 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824650 {A : Type'} (c : type686 A) (_59799 : A -> Prop) : (term237 A c _59799) = (term237 A c _59799).
Proof. exact (eq_refl (term237 A c _59799)). Qed.
Lemma lem4824651 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term368 A c _59801 _59800 _59799 _59802) = (term439 A _59799 _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824650 A c _59799) (@lem4824649 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824655 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824656 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term439 A _59799 _59801 _59802 c _59800) = (term440 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824655 (@I (A -> Prop) _59799 _59802) (term236 A c _59799) (term437 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824670 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824671 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term441 A _59799 _59801 _59802 c _59800) = (term442 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824670 (@I (A -> Prop) _59800 _59801) (term236 A c _59799) (term443 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824685 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824686 {A : Type'} (_59801 : A) (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term444 A _59799 _59801 _59802 c _59800) = (term445 A _59801 _59799 _59802 c _59800).
Proof. exact (@lem4824685 (term228 A _59799 _59801) (term236 A c _59799) (term394 A _59802 c _59800)). Qed.
Lemma lem4824700 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824701 {A : Type'} (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term446 A _59799 _59802 c _59800) = (term447 A _59802 _59799 c _59800).
Proof. exact (@lem4824700 (term228 A _59800 _59802) (term236 A c _59799) (term236 A c _59800)). Qed.
Lemma lem4824717 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term229 A _59799 _59801) = (term229 A _59799 _59801).
Proof. exact (eq_refl (term229 A _59799 _59801)). Qed.
Lemma lem4824718 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term445 A _59801 _59799 _59802 c _59800) = (term448 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824717 A _59799 _59801) (@lem4824701 A _59802 _59799 c _59800)). Qed.
Lemma lem4824729 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term444 A _59799 _59801 _59802 c _59800) = (term448 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824686 A _59801 _59799 _59802 c _59800) (@lem4824718 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824730 {A : Type'} (_59800 : A -> Prop) (_59801 : A) : (term430 A _59800 _59801) = (term430 A _59800 _59801).
Proof. exact (eq_refl (term430 A _59800 _59801)). Qed.
Lemma lem4824731 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term442 A _59799 _59801 _59802 c _59800) = (term449 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824730 A _59800 _59801) (@lem4824729 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824742 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term441 A _59799 _59801 _59802 c _59800) = (term449 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824671 A _59799 _59801 _59802 c _59800) (@lem4824731 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824743 {A : Type'} (_59799 : A -> Prop) (_59802 : A) : (term430 A _59799 _59802) = (term430 A _59799 _59802).
Proof. exact (eq_refl (term430 A _59799 _59802)). Qed.
Lemma lem4824744 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term440 A _59799 _59801 _59802 c _59800) = (term450 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824743 A _59799 _59802) (@lem4824742 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824755 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term439 A _59799 _59801 _59802 c _59800) = (term450 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824656 A _59799 _59801 _59802 c _59800) (@lem4824744 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824756 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term368 A c _59801 _59800 _59799 _59802) = (term450 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824651 A _59799 _59801 _59802 c _59800) (@lem4824755 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4824758 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term451 A c _59801 _59800 _59799 _59802) = (term452 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824757) (@lem4824756 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824782 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824783 {A : Type'} (_59799 : A -> Prop) (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term453 A c _59799 _59801 _59800 _59802) = (term454 A _59799 c _59801 _59800 _59802).
Proof. exact (@lem4824782 (term228 A _59799 _59801) (term236 A c _59800) (term455 A _59801 _59800 _59802)). Qed.
Lemma lem4824797 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824798 {A : Type'} (_59801 : A) (c : type686 A) (_59800 : A -> Prop) (_59802 : A) : (term456 A c _59801 _59800 _59802) = (term457 A _59801 c _59800 _59802).
Proof. exact (@lem4824797 (@I (A -> Prop) _59800 _59801) (term236 A c _59800) (term228 A _59800 _59802)). Qed.
Lemma lem4824812 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4824813 {A : Type'} (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term458 A c _59800 _59802) = (term394 A _59802 c _59800).
Proof. exact (@lem4824812 (term228 A _59800 _59802) (term236 A c _59800)). Qed.
Lemma lem4824819 {A : Type'} (_59800 : A -> Prop) (_59801 : A) : (term430 A _59800 _59801) = (term430 A _59800 _59801).
Proof. exact (eq_refl (term430 A _59800 _59801)). Qed.
Lemma lem4824820 {A : Type'} (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term457 A _59801 c _59800 _59802) = (term435 A _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824819 A _59800 _59801) (@lem4824813 A _59802 c _59800)). Qed.
Lemma lem4824831 {A : Type'} (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term456 A c _59801 _59800 _59802) = (term435 A _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824798 A _59801 c _59800 _59802) (@lem4824820 A _59801 _59802 c _59800)). Qed.
Lemma lem4824832 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term229 A _59799 _59801) = (term229 A _59799 _59801).
Proof. exact (eq_refl (term229 A _59799 _59801)). Qed.
Lemma lem4824833 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term454 A _59799 c _59801 _59800 _59802) = (term436 A _59799 _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824832 A _59799 _59801) (@lem4824831 A _59801 _59802 c _59800)). Qed.
Lemma lem4824837 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824838 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term436 A _59799 _59801 _59802 c _59800) = (term437 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824837 (@I (A -> Prop) _59800 _59801) (term228 A _59799 _59801) (term394 A _59802 c _59800)). Qed.
Lemma lem4824864 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term454 A _59799 c _59801 _59800 _59802) = (term437 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824833 A _59799 _59801 _59802 c _59800) (@lem4824838 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824865 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term453 A c _59799 _59801 _59800 _59802) = (term437 A _59799 _59801 _59802 c _59800).
Proof. exact (TRANS (@lem4824783 A _59799 c _59801 _59800 _59802) (@lem4824864 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824866 {A : Type'} (c : type686 A) (_59799 : A -> Prop) : (term237 A c _59799) = (term237 A c _59799).
Proof. exact (eq_refl (term237 A c _59799)). Qed.
Lemma lem4824867 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term459 A c _59799 _59801 _59800 _59802) = (term441 A _59799 _59801 _59802 c _59800).
Proof. exact (MK_COMB (@lem4824866 A c _59799) (@lem4824865 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824871 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824872 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term441 A _59799 _59801 _59802 c _59800) = (term442 A _59799 _59801 _59802 c _59800).
Proof. exact (@lem4824871 (@I (A -> Prop) _59800 _59801) (term236 A c _59799) (term443 A _59799 _59801 _59802 c _59800)). Qed.
Lemma lem4824886 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824887 {A : Type'} (_59801 : A) (_59799 : A -> Prop) (_59802 : A) (c : type686 A) (_59800 : A -> Prop) : (term444 A _59799 _59801 _59802 c _59800) = (term445 A _59801 _59799 _59802 c _59800).
Proof. exact (@lem4824886 (term228 A _59799 _59801) (term236 A c _59799) (term394 A _59802 c _59800)). Qed.
Lemma lem4824901 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4824902 {A : Type'} (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term446 A _59799 _59802 c _59800) = (term447 A _59802 _59799 c _59800).
Proof. exact (@lem4824901 (term228 A _59800 _59802) (term236 A c _59799) (term236 A c _59800)). Qed.
Lemma lem4824918 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term229 A _59799 _59801) = (term229 A _59799 _59801).
Proof. exact (eq_refl (term229 A _59799 _59801)). Qed.
Lemma lem4824919 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term445 A _59801 _59799 _59802 c _59800) = (term448 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824918 A _59799 _59801) (@lem4824902 A _59802 _59799 c _59800)). Qed.
Lemma lem4824930 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term444 A _59799 _59801 _59802 c _59800) = (term448 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824887 A _59801 _59799 _59802 c _59800) (@lem4824919 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824931 {A : Type'} (_59800 : A -> Prop) (_59801 : A) : (term430 A _59800 _59801) = (term430 A _59800 _59801).
Proof. exact (eq_refl (term430 A _59800 _59801)). Qed.
Lemma lem4824932 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term442 A _59799 _59801 _59802 c _59800) = (term449 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824931 A _59800 _59801) (@lem4824930 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824943 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term441 A _59799 _59801 _59802 c _59800) = (term449 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824872 A _59799 _59801 _59802 c _59800) (@lem4824932 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824944 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term459 A c _59799 _59801 _59800 _59802) = (term449 A _59801 _59802 _59799 c _59800).
Proof. exact (TRANS (@lem4824867 A _59799 _59801 _59802 c _59800) (@lem4824943 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824945 {A : Type'} (_59799 : A -> Prop) (_59802 : A) : (term430 A _59799 _59802) = (term430 A _59799 _59802).
Proof. exact (eq_refl (term430 A _59799 _59802)). Qed.
Lemma lem4824946 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : (term460 A c _59799 _59801 _59800 _59802) = (term450 A _59801 _59802 _59799 c _59800).
Proof. exact (MK_COMB (@lem4824945 A _59799 _59802) (@lem4824944 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824957 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : ((term368 A c _59801 _59800 _59799 _59802) = (term460 A c _59799 _59801 _59800 _59802)) = ((term450 A _59801 _59802 _59799 c _59800) = (term450 A _59801 _59802 _59799 c _59800)).
Proof. exact (MK_COMB (@lem4824758 A _59801 _59802 _59799 c _59800) (@lem4824946 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824959 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4824960 (x : Prop) : (x = x) = True.
Proof. exact (@lem4824959 Prop x). Qed.
Lemma lem4824961 {A : Type'} (_59801 : A) (_59802 : A) (_59799 : A -> Prop) (c : type686 A) (_59800 : A -> Prop) : ((term450 A _59801 _59802 _59799 c _59800) = (term450 A _59801 _59802 _59799 c _59800)) = True.
Proof. exact (@lem4824960 (term450 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824962 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : ((term368 A c _59801 _59800 _59799 _59802) = (term460 A c _59799 _59801 _59800 _59802)) = True.
Proof. exact (TRANS (@lem4824957 A _59801 _59802 _59799 c _59800) (@lem4824961 A _59801 _59802 _59799 c _59800)). Qed.
Lemma lem4824963 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : True = ((term368 A c _59801 _59800 _59799 _59802) = (term460 A c _59799 _59801 _59800 _59802)).
Proof. exact (SYM (@lem4824962 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4824964 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term368 A c _59801 _59800 _59799 _59802) = (term460 A c _59799 _59801 _59800 _59802).
Proof. exact (EQ_MP (@lem4824963 A c _59799 _59801 _59800 _59802) (@lem0)). Qed.
Lemma lem4824965 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term460 A c _59799 _59801 _59800 _59802.
Proof. exact (EQ_MP (@lem4824964 A c _59799 _59801 _59800 _59802) (@lem4823900 A _59801 _59800 _59799 _59802 R c h1)). Qed.
Lemma lem4824967 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4824968 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term460 A c _59799 _59801 _59800 _59802) = (term461 A c _59801 _59800 _59799 _59802).
Proof. exact (@lem4824967 (term459 A c _59799 _59801 _59800 _59802) (@I (A -> Prop) _59799 _59802)). Qed.
Lemma lem4824970 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824971 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term462 A c _59799 _59801 _59800 _59802) = (term463 A c _59799 _59801 _59800 _59802).
Proof. exact (@lem4824970 (term236 A c _59799) (term453 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4824973 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824974 {A : Type'} (c : type686 A) (_59799 : A -> Prop) : (term404 A c _59799) = (@I ((A -> Prop) -> Prop) c _59799).
Proof. exact (@lem4824973 (@I ((A -> Prop) -> Prop) c _59799)). Qed.
Lemma lem4824975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4824976 {A : Type'} (c : type686 A) (_59799 : A -> Prop) : (term405 A c _59799) = (term260 A c _59799).
Proof. exact (MK_COMB (@lem4824975) (@lem4824974 A c _59799)). Qed.
Lemma lem4824978 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824979 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term464 A c _59799 _59801 _59800 _59802) = (term465 A c _59799 _59801 _59800 _59802).
Proof. exact (@lem4824978 (term236 A c _59800) (term466 A _59799 _59801 _59800 _59802)). Qed.
Lemma lem4824981 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824982 {A : Type'} (c : type686 A) (_59800 : A -> Prop) : (term404 A c _59800) = (@I ((A -> Prop) -> Prop) c _59800).
Proof. exact (@lem4824981 (@I ((A -> Prop) -> Prop) c _59800)). Qed.
Lemma lem4824983 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4824984 {A : Type'} (c : type686 A) (_59800 : A -> Prop) : (term405 A c _59800) = (term260 A c _59800).
Proof. exact (MK_COMB (@lem4824983) (@lem4824982 A c _59800)). Qed.
Lemma lem4824986 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824987 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term467 A _59799 _59801 _59800 _59802) = (term468 A _59799 _59801 _59800 _59802).
Proof. exact (@lem4824986 (term228 A _59799 _59801) (term455 A _59801 _59800 _59802)). Qed.
Lemma lem4824989 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824990 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term408 A _59799 _59801) = (@I (A -> Prop) _59799 _59801).
Proof. exact (@lem4824989 (@I (A -> Prop) _59799 _59801)). Qed.
Lemma lem4824991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4824992 {A : Type'} (_59799 : A -> Prop) (_59801 : A) : (term409 A _59799 _59801) = (term410 A _59799 _59801).
Proof. exact (MK_COMB (@lem4824991) (@lem4824990 A _59799 _59801)). Qed.
Lemma lem4824994 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4824995 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term469 A _59801 _59800 _59802) = (term470 A _59801 _59800 _59802).
Proof. exact (@lem4824994 (@I (A -> Prop) _59800 _59801) (term228 A _59800 _59802)). Qed.
Lemma lem4824997 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4824998 {A : Type'} (_59800 : A -> Prop) (_59802 : A) : (term408 A _59800 _59802) = (@I (A -> Prop) _59800 _59802).
Proof. exact (@lem4824997 (@I (A -> Prop) _59800 _59802)). Qed.
Lemma lem4824999 {A : Type'} (_59800 : A -> Prop) (_59801 : A) : (term471 A _59800 _59801) = (term471 A _59800 _59801).
Proof. exact (eq_refl (term471 A _59800 _59801)). Qed.
Lemma lem4825000 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term470 A _59801 _59800 _59802) = (term472 A _59801 _59800 _59802).
Proof. exact (MK_COMB (@lem4824999 A _59800 _59801) (@lem4824998 A _59800 _59802)). Qed.
Lemma lem4825001 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term469 A _59801 _59800 _59802) = (term472 A _59801 _59800 _59802).
Proof. exact (TRANS (@lem4824995 A _59801 _59800 _59802) (@lem4825000 A _59801 _59800 _59802)). Qed.
Lemma lem4825002 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term468 A _59799 _59801 _59800 _59802) = (term473 A _59799 _59801 _59800 _59802).
Proof. exact (MK_COMB (@lem4824992 A _59799 _59801) (@lem4825001 A _59801 _59800 _59802)). Qed.
Lemma lem4825003 {A : Type'} (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term467 A _59799 _59801 _59800 _59802) = (term473 A _59799 _59801 _59800 _59802).
Proof. exact (TRANS (@lem4824987 A _59799 _59801 _59800 _59802) (@lem4825002 A _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825004 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term465 A c _59799 _59801 _59800 _59802) = (term474 A c _59799 _59801 _59800 _59802).
Proof. exact (MK_COMB (@lem4824984 A c _59800) (@lem4825003 A _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825005 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term464 A c _59799 _59801 _59800 _59802) = (term474 A c _59799 _59801 _59800 _59802).
Proof. exact (TRANS (@lem4824979 A c _59799 _59801 _59800 _59802) (@lem4825004 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825006 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term463 A c _59799 _59801 _59800 _59802) = (term475 A c _59799 _59801 _59800 _59802).
Proof. exact (MK_COMB (@lem4824976 A c _59799) (@lem4825005 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825007 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term462 A c _59799 _59801 _59800 _59802) = (term475 A c _59799 _59801 _59800 _59802).
Proof. exact (TRANS (@lem4824971 A c _59799 _59801 _59800 _59802) (@lem4825006 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4825009 {A : Type'} (c : type686 A) (_59799 : A -> Prop) (_59801 : A) (_59800 : A -> Prop) (_59802 : A) : (term476 A c _59799 _59801 _59800 _59802) = (term477 A c _59799 _59801 _59800 _59802).
Proof. exact (MK_COMB (@lem4825008) (@lem4825007 A c _59799 _59801 _59800 _59802)). Qed.
Lemma lem4825010 {A : Type'} (_59799 : A -> Prop) (_59802 : A) : (@I (A -> Prop) _59799 _59802) = (@I (A -> Prop) _59799 _59802).
Proof. exact (eq_refl (@I (A -> Prop) _59799 _59802)). Qed.
Lemma lem4825011 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term461 A c _59801 _59800 _59799 _59802) = (term478 A c _59801 _59800 _59799 _59802).
Proof. exact (MK_COMB (@lem4825009 A c _59799 _59801 _59800 _59802) (@lem4825010 A _59799 _59802)). Qed.
Lemma lem4825012 {A : Type'} (c : type686 A) (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) : (term460 A c _59799 _59801 _59800 _59802) = (term478 A c _59801 _59800 _59799 _59802).
Proof. exact (TRANS (@lem4824968 A c _59801 _59800 _59799 _59802) (@lem4825011 A c _59801 _59800 _59799 _59802)). Qed.
Lemma lem4825014 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term472 A x t' y.
Proof. exact (conj (@lem4824455 A R t c t' x y h1 h2 h3 h4) (@lem4824462 A t c t' x y h4)). Qed.
Lemma lem4825015 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term473 A t x t' y.
Proof. exact (conj (@lem4823996 A t c t' x y h4) (@lem4825014 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825016 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term474 A c t x t' y.
Proof. exact (conj (@lem4823989 A t c t' x y h4) (@lem4825015 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825017 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term475 A c t x t' y.
Proof. exact (conj (@lem4823982 A t c t' x y h4) (@lem4825016 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825019 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term478 A c _59801 _59800 _59799 _59802.
Proof. exact (EQ_MP (@lem4825012 A c _59801 _59800 _59799 _59802) (@lem4824965 A _59799 _59801 _59800 _59802 R c h1)). Qed.
Lemma lem4825020 {A : Type'} (_59801 : A) (_59800 : A -> Prop) (_59799 : A -> Prop) (_59802 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term478 A c _59801 _59800 _59799 _59802.
Proof. exact (@lem4825019 A _59801 _59800 _59799 _59802 R c h1). Qed.
Lemma lem4825021 {A : Type'} (x : A) (t' : A -> Prop) (t : A -> Prop) (y : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term478 A c x t' t y.
Proof. exact (@lem4825020 A x t' t y R c h1). Qed.
Lemma lem4825024 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : @I (A -> Prop) t y.
Proof. exact (@lem4825021 A x t' t y R c h3 (@lem4825017 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825025 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term371 A t y.
Proof. exact (fun h0 : term228 A t y => @lem4825024 A R t c t' x y h1 h2 h3 h4). Qed.
Lemma lem4825027 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4825028 {A : Type'} (t : A -> Prop) (y : A) : (term371 A t y) = (@I (A -> Prop) t y).
Proof. exact (@lem4825027 (@I (A -> Prop) t y)). Qed.
Lemma lem4825029 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : @I (A -> Prop) t y.
Proof. exact (EQ_MP (@lem4825028 A t y) (@lem4825025 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825031 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term259 A R x y.
Proof. exact (EQ_MP (@lem4823503 A R x y) (@lem4823322 A R x y h1)). Qed.
Lemma lem4825032 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term374 A R x y.
Proof. exact (fun h0 : term245 A R x y => @lem4825031 A R x y h1). Qed.
Lemma lem4825034 (p : Prop) : (term373 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4825035 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term374 A R x y) = (term259 A R x y).
Proof. exact (@lem4825034 (term245 A R x y)). Qed.
Lemma lem4825036 {A : Type'} (R : type1402 A) (x : A) (y : A) (h1 : term141 A R x y) : term259 A R x y.
Proof. exact (EQ_MP (@lem4825035 A R x y) (@lem4825032 A R x y h1)). Qed.
Lemma lem4825042 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825043 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term365 A c _59796 R _59797 _59798) = (term375 A c _59796 R _59797 _59798).
Proof. exact (@lem4825042 (term228 A _59796 _59797) (term236 A c _59796) (term363 A _59796 R _59797 _59798)). Qed.
Lemma lem4825057 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825058 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term376 A c _59796 R _59797 _59798) = (term377 A c _59796 R _59797 _59798).
Proof. exact (@lem4825057 (term228 A _59796 _59798) (term236 A c _59796) (term378 A R _59797 _59798)). Qed.
Lemma lem4825072 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825073 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term379 A c _59796 R _59797 _59798) = (term380 A c _59796 R _59797 _59798).
Proof. exact (@lem4825072 (_59797 = _59798) (term236 A c _59796) (term245 A R _59797 _59798)). Qed.
Lemma lem4825089 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4825090 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term381 A c _59796 R _59797 _59798) = (term382 A R _59797 _59798 c _59796).
Proof. exact (@lem4825089 (term245 A R _59797 _59798) (term236 A c _59796)). Qed.
Lemma lem4825096 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4825097 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term380 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825096 A _59797 _59798) (@lem4825090 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825108 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term379 A c _59796 R _59797 _59798) = (term384 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825073 A c _59796 R _59797 _59798) (@lem4825097 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825109 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term229 A _59796 _59798) = (term229 A _59796 _59798).
Proof. exact (eq_refl (term229 A _59796 _59798)). Qed.
Lemma lem4825110 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term385 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825109 A _59796 _59798) (@lem4825108 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825114 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825115 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term386 A R _59797 _59798 c _59796).
Proof. exact (@lem4825114 (_59797 = _59798) (term228 A _59796 _59798) (term382 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825131 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825132 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term387 A R _59797 _59798 c _59796) = (term388 A R _59797 _59798 c _59796).
Proof. exact (@lem4825131 (term245 A R _59797 _59798) (term228 A _59796 _59798) (term236 A c _59796)). Qed.
Lemma lem4825148 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4825149 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term386 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825148 A _59797 _59798) (@lem4825132 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825160 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term385 A R _59797 _59798 c _59796) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825115 A R _59797 _59798 c _59796) (@lem4825149 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825161 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term377 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825110 A R _59797 _59798 c _59796) (@lem4825160 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825162 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term376 A c _59796 R _59797 _59798) = (term389 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825058 A c _59796 R _59797 _59798) (@lem4825161 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825163 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term229 A _59796 _59797) = (term229 A _59796 _59797).
Proof. exact (eq_refl (term229 A _59796 _59797)). Qed.
Lemma lem4825164 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term390 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825163 A _59796 _59797) (@lem4825162 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825168 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825169 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term391 A R _59797 _59798 c _59796).
Proof. exact (@lem4825168 (_59797 = _59798) (term228 A _59796 _59797) (term388 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825185 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825186 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term392 A R _59797 _59798 c _59796) = (term393 A R _59797 _59798 c _59796).
Proof. exact (@lem4825185 (term245 A R _59797 _59798) (term228 A _59796 _59797) (term394 A _59798 c _59796)). Qed.
Lemma lem4825212 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4825213 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term391 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825212 A _59797 _59798) (@lem4825186 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825224 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term390 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825169 A R _59797 _59798 c _59796) (@lem4825213 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825225 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term375 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825164 A R _59797 _59798 c _59796) (@lem4825224 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825226 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term365 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825043 A c _59796 R _59797 _59798) (@lem4825225 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4825228 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term396 A c _59796 R _59797 _59798) = (term397 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825227) (@lem4825226 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825244 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825245 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term479 A c _59796 R _59797 _59798) = (term480 A c _59796 R _59797 _59798).
Proof. exact (@lem4825244 (term228 A _59796 _59797) (term236 A c _59796) (term481 A _59796 R _59797 _59798)). Qed.
Lemma lem4825259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825260 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term482 A c _59796 R _59797 _59798) = (term483 A c _59796 R _59797 _59798).
Proof. exact (@lem4825259 (term228 A _59796 _59798) (term236 A c _59796) (term245 A R _59797 _59798)). Qed.
Lemma lem4825274 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4825275 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term381 A c _59796 R _59797 _59798) = (term382 A R _59797 _59798 c _59796).
Proof. exact (@lem4825274 (term245 A R _59797 _59798) (term236 A c _59796)). Qed.
Lemma lem4825281 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term229 A _59796 _59798) = (term229 A _59796 _59798).
Proof. exact (eq_refl (term229 A _59796 _59798)). Qed.
Lemma lem4825282 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term483 A c _59796 R _59797 _59798) = (term387 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825281 A _59796 _59798) (@lem4825275 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825286 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825287 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term387 A R _59797 _59798 c _59796) = (term388 A R _59797 _59798 c _59796).
Proof. exact (@lem4825286 (term245 A R _59797 _59798) (term228 A _59796 _59798) (term236 A c _59796)). Qed.
Lemma lem4825303 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term483 A c _59796 R _59797 _59798) = (term388 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825282 A R _59797 _59798 c _59796) (@lem4825287 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825304 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term482 A c _59796 R _59797 _59798) = (term388 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825260 A c _59796 R _59797 _59798) (@lem4825303 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825305 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term229 A _59796 _59797) = (term229 A _59796 _59797).
Proof. exact (eq_refl (term229 A _59796 _59797)). Qed.
Lemma lem4825306 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term480 A c _59796 R _59797 _59798) = (term392 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825305 A _59796 _59797) (@lem4825304 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825310 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4825311 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term392 A R _59797 _59798 c _59796) = (term393 A R _59797 _59798 c _59796).
Proof. exact (@lem4825310 (term245 A R _59797 _59798) (term228 A _59796 _59797) (term394 A _59798 c _59796)). Qed.
Lemma lem4825337 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term480 A c _59796 R _59797 _59798) = (term393 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825306 A R _59797 _59798 c _59796) (@lem4825311 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825338 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term479 A c _59796 R _59797 _59798) = (term393 A R _59797 _59798 c _59796).
Proof. exact (TRANS (@lem4825245 A c _59796 R _59797 _59798) (@lem4825337 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825339 {A : Type'} (_59797 : A) (_59798 : A) : (term383 A _59797 _59798) = (term383 A _59797 _59798).
Proof. exact (eq_refl (term383 A _59797 _59798)). Qed.
Lemma lem4825340 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : (term484 A c _59796 R _59797 _59798) = (term395 A R _59797 _59798 c _59796).
Proof. exact (MK_COMB (@lem4825339 A _59797 _59798) (@lem4825338 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825351 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : ((term365 A c _59796 R _59797 _59798) = (term484 A c _59796 R _59797 _59798)) = ((term395 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796)).
Proof. exact (MK_COMB (@lem4825228 A R _59797 _59798 c _59796) (@lem4825340 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4825354 (x : Prop) : (x = x) = True.
Proof. exact (@lem4825353 Prop x). Qed.
Lemma lem4825355 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) (c : type686 A) (_59796 : A -> Prop) : ((term395 A R _59797 _59798 c _59796) = (term395 A R _59797 _59798 c _59796)) = True.
Proof. exact (@lem4825354 (term395 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825356 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : ((term365 A c _59796 R _59797 _59798) = (term484 A c _59796 R _59797 _59798)) = True.
Proof. exact (TRANS (@lem4825351 A R _59797 _59798 c _59796) (@lem4825355 A R _59797 _59798 c _59796)). Qed.
Lemma lem4825357 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : True = ((term365 A c _59796 R _59797 _59798) = (term484 A c _59796 R _59797 _59798)).
Proof. exact (SYM (@lem4825356 A c _59796 R _59797 _59798)). Qed.
Lemma lem4825358 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term365 A c _59796 R _59797 _59798) = (term484 A c _59796 R _59797 _59798).
Proof. exact (EQ_MP (@lem4825357 A c _59796 R _59797 _59798) (@lem0)). Qed.
Lemma lem4825359 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term484 A c _59796 R _59797 _59798.
Proof. exact (EQ_MP (@lem4825358 A c _59796 R _59797 _59798) (@lem4823874 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4825361 (b : Prop) (a : Prop) : (a \/ b) = (term398 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4825362 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term484 A c _59796 R _59797 _59798) = (term485 A c _59796 R _59797 _59798).
Proof. exact (@lem4825361 (term479 A c _59796 R _59797 _59798) (_59797 = _59798)). Qed.
Lemma lem4825364 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4825365 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term486 A c _59796 R _59797 _59798) = (term487 A c _59796 R _59797 _59798).
Proof. exact (@lem4825364 (term236 A c _59796) (term488 A _59796 R _59797 _59798)). Qed.
Lemma lem4825367 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4825368 {A : Type'} (c : type686 A) (_59796 : A -> Prop) : (term404 A c _59796) = (@I ((A -> Prop) -> Prop) c _59796).
Proof. exact (@lem4825367 (@I ((A -> Prop) -> Prop) c _59796)). Qed.
Lemma lem4825369 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825370 {A : Type'} (c : type686 A) (_59796 : A -> Prop) : (term405 A c _59796) = (term260 A c _59796).
Proof. exact (MK_COMB (@lem4825369) (@lem4825368 A c _59796)). Qed.
Lemma lem4825372 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4825373 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term489 A _59796 R _59797 _59798) = (term490 A _59796 R _59797 _59798).
Proof. exact (@lem4825372 (term228 A _59796 _59797) (term481 A _59796 R _59797 _59798)). Qed.
Lemma lem4825375 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4825376 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term408 A _59796 _59797) = (@I (A -> Prop) _59796 _59797).
Proof. exact (@lem4825375 (@I (A -> Prop) _59796 _59797)). Qed.
Lemma lem4825377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825378 {A : Type'} (_59796 : A -> Prop) (_59797 : A) : (term409 A _59796 _59797) = (term410 A _59796 _59797).
Proof. exact (MK_COMB (@lem4825377) (@lem4825376 A _59796 _59797)). Qed.
Lemma lem4825380 (a : Prop) (b : Prop) : (term400 a b) = (term401 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4825381 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term491 A _59796 R _59797 _59798) = (term492 A _59796 R _59797 _59798).
Proof. exact (@lem4825380 (term228 A _59796 _59798) (term245 A R _59797 _59798)). Qed.
Lemma lem4825383 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4825384 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term408 A _59796 _59798) = (@I (A -> Prop) _59796 _59798).
Proof. exact (@lem4825383 (@I (A -> Prop) _59796 _59798)). Qed.
Lemma lem4825385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4825386 {A : Type'} (_59796 : A -> Prop) (_59798 : A) : (term409 A _59796 _59798) = (term410 A _59796 _59798).
Proof. exact (MK_COMB (@lem4825385) (@lem4825384 A _59796 _59798)). Qed.
Lemma lem4825387 {A : Type'} (R : type1402 A) (_59797 : A) (_59798 : A) : (term259 A R _59797 _59798) = (term259 A R _59797 _59798).
Proof. exact (eq_refl (term259 A R _59797 _59798)). Qed.
Lemma lem4825388 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term492 A _59796 R _59797 _59798) = (term493 A _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4825386 A _59796 _59798) (@lem4825387 A R _59797 _59798)). Qed.
Lemma lem4825389 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term491 A _59796 R _59797 _59798) = (term493 A _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4825381 A _59796 R _59797 _59798) (@lem4825388 A _59796 R _59797 _59798)). Qed.
Lemma lem4825390 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term490 A _59796 R _59797 _59798) = (term494 A _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4825378 A _59796 _59797) (@lem4825389 A _59796 R _59797 _59798)). Qed.
Lemma lem4825391 {A : Type'} (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term489 A _59796 R _59797 _59798) = (term494 A _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4825373 A _59796 R _59797 _59798) (@lem4825390 A _59796 R _59797 _59798)). Qed.
Lemma lem4825392 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term487 A c _59796 R _59797 _59798) = (term495 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4825370 A c _59796) (@lem4825391 A _59796 R _59797 _59798)). Qed.
Lemma lem4825393 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term486 A c _59796 R _59797 _59798) = (term495 A c _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4825365 A c _59796 R _59797 _59798) (@lem4825392 A c _59796 R _59797 _59798)). Qed.
Lemma lem4825394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4825395 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term496 A c _59796 R _59797 _59798) = (term497 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4825394) (@lem4825393 A c _59796 R _59797 _59798)). Qed.
Lemma lem4825396 {A : Type'} (_59797 : A) (_59798 : A) : (_59797 = _59798) = (_59797 = _59798).
Proof. exact (eq_refl (_59797 = _59798)). Qed.
Lemma lem4825397 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term485 A c _59796 R _59797 _59798) = (term498 A c _59796 R _59797 _59798).
Proof. exact (MK_COMB (@lem4825395 A c _59796 R _59797 _59798) (@lem4825396 A _59797 _59798)). Qed.
Lemma lem4825398 {A : Type'} (c : type686 A) (_59796 : A -> Prop) (R : type1402 A) (_59797 : A) (_59798 : A) : (term484 A c _59796 R _59797 _59798) = (term498 A c _59796 R _59797 _59798).
Proof. exact (TRANS (@lem4825362 A c _59796 R _59797 _59798) (@lem4825397 A c _59796 R _59797 _59798)). Qed.
Lemma lem4825400 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term493 A t R x y.
Proof. exact (conj (@lem4825029 A R t c t' x y h1 h2 h3 h4) (@lem4825036 A R x y h2)). Qed.
Lemma lem4825401 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term494 A t R x y.
Proof. exact (conj (@lem4823975 A t c t' x y h4) (@lem4825400 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825402 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : term495 A c t R x y.
Proof. exact (conj (@lem4823968 A t c t' x y h4) (@lem4825401 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825404 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term498 A c _59796 R _59797 _59798.
Proof. exact (EQ_MP (@lem4825398 A c _59796 R _59797 _59798) (@lem4825359 A _59796 _59797 _59798 R c h1)). Qed.
Lemma lem4825405 {A : Type'} (_59796 : A -> Prop) (_59797 : A) (_59798 : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term498 A c _59796 R _59797 _59798.
Proof. exact (@lem4825404 A _59796 _59797 _59798 R c h1). Qed.
Lemma lem4825406 {A : Type'} (t : A -> Prop) (x : A) (y : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term498 A c t R x y.
Proof. exact (@lem4825405 A t x y R c h1). Qed.
Lemma lem4825409 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term62 A x y) (h2 : term141 A R x y) (h3 : term101 A R c) (h4 : term221 A t c t' x y) : x = y.
Proof. exact (@lem4825406 A t x y R c h3 (@lem4825402 A R t c t' x y h1 h2 h3 h4)). Qed.
Lemma lem4825410 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term221 A t c t' x y) : term499 A x y.
Proof. exact (fun h0 : term62 A x y => @lem4825409 A R t c t' x y h0 h1 h2 h3). Qed.
Lemma lem4825412 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4825413 {A : Type'} (x : A) (y : A) : (term499 A x y) = (x = y).
Proof. exact (@lem4825412 (x = y)). Qed.
Lemma lem4825414 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term221 A t c t' x y) : x = y.
Proof. exact (EQ_MP (@lem4825413 A x y) (@lem4825410 A R t c t' x y h1 h2 h3)). Qed.
Lemma lem4825417 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4825419 {A : Type'} (x : A) (y : A) : (term62 A x y) = (term500 A x y).
Proof. exact (@lem4825417 (x = y)). Qed.
Lemma lem4825422 {A : Type'} (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term221 A t c t' x y) : term500 A x y.
Proof. exact (EQ_MP (@lem4825419 A x y) (@lem4823844 A t c t' x y h1)). Qed.
Lemma lem4825425 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term221 A t c t' x y) : False.
Proof. exact (@lem4825422 A t c t' x y h3 (@lem4825414 A R t c t' x y h1 h2 h3)). Qed.
Lemma lem4825426 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term221 A t c t' x y) : term501.
Proof. exact (fun h0 : ~ False => @lem4825425 A R t c t' x y h1 h2 h3). Qed.
Lemma lem4825428 (p : Prop) : (term370 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4825429 : term501 = False.
Proof. exact (@lem4825428 False). Qed.
Lemma lem4825430 {A : Type'} (R : type1402 A) (t : A -> Prop) (c : type686 A) (t' : A -> Prop) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term221 A t c t' x y) : False.
Proof. exact (EQ_MP (@lem4825429) (@lem4825426 A R t c t' x y h1 h2 h3)). Qed.
Lemma lem4825431 {A : Type'} (t : A -> Prop) (x : A) (y : A) (R : type1402 A) (c : type686 A) (h1 : term224 A t c x y) (h2 : term141 A R x y) (h3 : term101 A R c) : False.
Proof. exact (ex_elim (@lem4823323 A t c x y h1) (fun t' : A -> Prop => fun h0 : term223 A t c x y t' => @lem4825430 A R t c t' x y h2 h3 h0)). Qed.
Lemma lem4825432 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term115 A c x y) : False.
Proof. exact (ex_elim (@lem4823316 A c x y h3) (fun t : A -> Prop => fun h0 : term225 A c x y t => @lem4825431 A t x y R c h0 h1 h2)). Qed.
Lemma lem4825433 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term115 A c x y) : (term141 A R x y) = False.
Proof. exact (prop_ext (fun h4 : term141 A R x y => @lem4825432 A R c x y h1 h2 h3) (fun h4 : False => @lem4823322 A R x y h1)). Qed.
Lemma lem4825434 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term115 A c x y) : False.
Proof. exact (EQ_MP (@lem4825433 A R c x y h1 h2 h3) (@lem4823322 A R x y h1)). Qed.
Lemma lem4825435 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term115 A c x y) : (term141 A R x y) = False.
Proof. exact (prop_ext (fun h4 : term141 A R x y => @lem4825434 A R c x y h1 h2 h3) (fun h4 : False => @lem4822857 A R x y h1)). Qed.
Lemma lem4825436 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term141 A R x y) (h2 : term101 A R c) (h3 : term115 A c x y) : False.
Proof. exact (EQ_MP (@lem4825435 A R c x y h1 h2 h3) (@lem4822857 A R x y h1)). Qed.
Lemma lem4825437 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term101 A R c) (h2 : term115 A c x y) : term140 A R x y.
Proof. exact (fun h0 : term141 A R x y => @lem4825436 A R c x y h0 h1 h2). Qed.
Lemma lem4825438 {A : Type'} (R : type1402 A) (c : type686 A) (x : A) (y : A) (h1 : term101 A R c) (h2 : term115 A c x y) : R x y.
Proof. exact (EQ_MP (@lem4822856 A R x y) (@lem4825437 A R c x y h1 h2)). Qed.
Lemma lem4825439 {A : Type'} (x : A) (y : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term119 A c R x y.
Proof. exact (fun h0 : term115 A c x y => @lem4825438 A R c x y h1 h0). Qed.
Lemma lem4825444 {A : Type'} (x : A) (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term123 A c R x.
Proof. exact (fun y : A => @lem4825439 A x y R c h1). Qed.
Lemma lem4825449 {A : Type'} (R : type1402 A) (c : type686 A) (h1 : term101 A R c) : term126 A c R.
Proof. exact (fun x : A => @lem4825444 A x R c h1). Qed.
Lemma lem4825450 {A : Type'} (c : type686 A) (R : type1402 A) : term127 A c R.
Proof. exact (fun h0 : term101 A R c => @lem4825449 A R c h0). Qed.
Lemma lem4825455 {A : Type'} (R : type1402 A) : term129 A R.
Proof. exact (fun c : type686 A => @lem4825450 A c R). Qed.
Lemma lem4825460 {A : Type'} : term131 A.
Proof. exact (fun R : type1402 A => @lem4825455 A R). Qed.
Lemma lem4825461 {A : Type'} : term133 A.
Proof. exact (EQ_MP (@lem4822850 A) (@lem4825460 A)). Qed.
Lemma lem4825463 {A : Type'} : term133 A.
Proof. exact (@lem4822485 A (@lem4825461 A)). Qed.
Lemma lem4825464 {A : Type'} (h1 : term134 A) : False.
Proof. exact (@lem4825463 A (@lem4822469 A h1)). Qed.
Lemma lem4825465 {A : Type'} (h1 : term134 A) : (term134 A) = False.
Proof. exact (prop_ext (fun h2 : term134 A => @lem4825464 A h1) (fun h2 : False => @lem4822469 A h1)). Qed.
Lemma lem4825466 {A : Type'} (h1 : term134 A) : False.
Proof. exact (EQ_MP (@lem4825465 A h1) (@lem4822469 A h1)). Qed.
Lemma lem4825467 {A : Type'} : term133 A.
Proof. exact (fun h0 : term134 A => @lem4825466 A h0). Qed.
Lemma lem4825468 {A : Type'} : term131 A.
Proof. exact (EQ_MP (@lem4822468 A) (@lem4825467 A)). Qed.
Lemma lem4825469 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem4822464 A) (@lem4825468 A)). Qed.
Lemma lem4825470 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem4822138 A) (@lem4825469 A)). Qed.
Lemma lem4825471 {A : Type'} : term35 A.
Proof. exact (EQ_MP (@lem4822003 A) (@lem4825470 A)). Qed.
