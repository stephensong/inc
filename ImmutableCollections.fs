module ImmutableCollections

open System.Collections.Generic
#if IMMUTABLES
open System.Collections.Immutable

type PersistentMap<'k,'v> =  ImmutableSortedDictionary<'k,'v>

type ImmutableSortedDictionary<'k,'v> with
    static member ofSeq(coll) = ImmutableSortedDictionary.ToImmutableSortedDictionary<'k,'v>(coll)
    static member ofPairs(coll) = ImmutableSortedDictionary.ToImmutableSortedDictionary<'k,'v>(seq {for k,v in coll -> KeyValuePair(k,v)})

    member this.extend(prs) = this.SetItems(seq {for k,v in prs -> KeyValuePair(k,v)})

#else

type PersistentMap<'k,'v when 'k : comparison> = Map<'k,'v>

type Map<'k,'v when 'k : comparison> with

    static member ofSeq(coll : IDictionary<'k,'v>) = Map.ofSeq(seq {for kvp in coll -> kvp.Key,kvp.Value})
    static member ofPairs(coll) = Map(coll)
    static member Empty = Map<'k,'v>([])
    member this.SetItem(k,v) = this.Add(k,v)
    member this.extend(prs) =  
        let mutable rslt = this
        for k,v in prs do rslt <- rslt.Add(k,v)
        rslt
#endif
