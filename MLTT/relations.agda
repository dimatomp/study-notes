open import Agda.Primitive

-- It seems that we're unable to manage without Agda type levels any further.
-- Similarly to Set, Prop and Type in Coq, here we have Set and Set₁.
-- The latter corresponds to all types mentioning Set, while Set contains nothing mentioning itself to avoid the paradox.
-- In Agda, this approach is generalized, i.e. for any natural n, Setₙ is a valid type.

record _/\_ {ξ η : Level} (A : Set ξ) (B : Set η) : Set (ξ ⊔ η) where
  constructor _,_
  field
    fst : A
    snd : B

-- lsuc is for (+1). Basically, if S : Set, Relation S should be of Set₁.
record Relation {ξ η : Level} (S : Set ξ) : Set (lsuc (ξ ⊔ η)) where
  constructor define
  field
    apply : S -> S -> Set η

-- Try not to pay attention on the levels. In common cases all this stuff should be inferred to regular Sets.
reflexive : {ξ η : Level} {S : Set ξ} -> Relation {η = η} S -> Set (ξ ⊔ η)
reflexive {_} {_} {S} (define apply) = (s : S) -> apply s s

symmetric : {ξ η : Level} {S : Set ξ} -> Relation {η = η} S -> Set (ξ ⊔ η)
symmetric {_} {_} {S} (define apply) = (a b : S) -> apply a b -> apply b a

transitive : {ξ η : Level} {S : Set ξ} -> Relation {η = η} S -> Set (ξ ⊔ η)
transitive {_} {_} {S} (define apply) = (a b c : S) -> apply a b -> apply b c -> apply a c

equality : {ξ η : Level} {S : Set ξ} -> Relation {η = η} S -> Set (ξ ⊔ η)
equality rel = (reflexive rel /\ symmetric rel) /\ transitive rel

included : {ξ η₁ η₂ : Level} {S : Set ξ} -> Relation {η = η₁} S -> Relation {η = η₂} S -> Set (ξ ⊔ η₁ ⊔ η₂)
included {_} {_} {_} {S} (define apply1) (define apply2) = (a b : S) -> apply1 a b -> apply2 a b

equal : {ξ η₁ η₂ : Level} {S : Set ξ} -> Relation {η = η₁} S -> Relation {η = η₂} S -> Set (ξ ⊔ η₁ ⊔ η₂)
equal rel1 rel2 = included rel1 rel2 /\ included rel2 rel1

minimal : {S : Set} -> Relation {η = lzero} S -> Set₁
minimal {S} rel = (rel' : Relation {η = lzero} S) -> reflexive {lzero} rel' -> included {lzero} rel rel'

extensional : {A B : Set} -> Relation A -> Relation B -> (A -> B) -> Set
extensional {A} (define apply1) (define apply2) f = (x y : A) -> apply1 x y -> apply2 (f x) (f y)

theorem_about_min_refl_relation : {A : Set} {rel : Relation A} {hReflexive : reflexive rel} {hMinimal : minimal rel}
                               -> equality rel /\ ({B : Set} -> (rel' : Relation B) -> equality rel' -> (f : A -> B) -> extensional rel rel' f)
theorem_about_min_refl_relation {A} {rel} {hReflexive} {hMinimal} = (((hReflexive , isSymm) , isTrans) , extensionality)
  where
    relS = Relation.define (\x y -> Relation.apply rel y x)
    isSymm = hMinimal relS hReflexive

    relT = Relation.define (\x y -> (z : A) -> Relation.apply rel y z -> Relation.apply rel x z)
    minT = hMinimal relT (\x _ rel -> rel)
    isTrans : transitive rel
    isTrans a b c x x₁ = minT a b x c x₁

    extensionality : {B : Set} -> (rel' : Relation B) -> equality rel' -> (f : A -> B) -> extensional rel rel' f
    extensionality rel' ((refl' , _) , _) f a b p = hMinimal relF (\x -> refl' (f x)) a b p
      where relF = Relation.define (\x y -> Relation.apply rel' (f x) (f y))

-- The only place for which we needed to delve into levels so much. Here we define a relation of relations.
rels_equality_is_equivalence : {ξ η : Level} {S : Set ξ} -> equality (Relation.define (equal {ξ} {η} {η} {S}))
rels_equality_is_equivalence = {!!}
