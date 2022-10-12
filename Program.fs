 open System.IO
open System.Text.RegularExpressions
open System


module CaesarCipher =


    let cleanString str = let s = Regex.Replace(str, "[^A-ZÖÄÅ0-9(),.'\" \\n]", "") in s.Split [|' '|]

    let getWords path =
        let helper (streamReader : StreamReader) : option<string> =
            let x = streamReader.Peek() in
            match x with
            | x when x > -1 -> Some (streamReader.ReadLine())
            | _ -> None
        let fp = File.OpenText(path)
        let rec readFromFile (acc: string list) filePointer =
            match (helper filePointer) with
            | Some(x) -> readFromFile (x::acc) filePointer
            | None ->   filePointer.Close()
                        acc
        readFromFile [] fp



    let compare (cipherLst : string list) (freqLst : string list) =
        let rec comparehelper list acc =
            match list with
            | x::xs -> comparehelper xs ((if List.exists (fun y -> y = x) freqLst then 1 else 0) + acc)
            | [] -> acc
        comparehelper cipherLst 0


    let decipher (strLst: string list) =
        let freqwords = getWords "../../../freqWords.txt"

        let incrementChar (ch:char) count =
            let str = string ch in
            if Regex.IsMatch(str, "[^A-ZÖÄÅ ]") then ch
            else let value = ((int) ch + count) in let ans = ((value-65) % (90-65+1)) + 65
                 char ans

        let changeWord list count = List.fold (fun init ch -> (incrementChar ch count) :: init) [] list

        let concatCharList list = List.fold (fun init ch -> (string ch) + init) "" list

        let makestring x count =
            let charlist = Seq.toList x
            changeWord charlist count |> concatCharList

        let makeDecipher strList count = List.fold (fun init str -> (makestring str count) :: init) [] strList



        let getFreq list = compare list freqwords


        let toLower (list: string list) = List.fold (fun init (word: string) -> word.ToLower() :: init) [] list

        let rec getLikelyDeciphers listofwords average acc counter =
            let newlist = List.rev (makeDecipher listofwords counter) in
            let lower = toLower newlist in
            match ((getFreq lower), counter) with
            | (_, 25) -> acc
            | (x, counter) when x >= average -> getLikelyDeciphers listofwords ((average + x)/2) ((x, newlist)::acc) (counter + 1)
            | (x, counter) when x < average -> getLikelyDeciphers listofwords average acc (counter + 1)
            | _ -> failwith "this cant happen"
        getLikelyDeciphers strLst 0 [] 0

    let printList list = List.map (fun word -> printf "%s " word; word) list

    let rec debugprintList list =
        match list with
        | [] -> ()
        | (x, y)::xs -> printf "\n\n\n%d: \n" x ; printList y |> ignore ; debugprintList xs


    let dostuff listlist number =
        let rec dostuffhelper listlist i =
            match (listlist, i) with
            | ([], _) -> ()
            | (_, 0) -> ()
            | ((x, y)::xs, _) -> printList y |> ignore ; printf "\n\n\n"; dostuffhelper xs (i - 1)
        dostuffhelper listlist number

    let rec askUserHelper input lst =
        match (input, lst) with
        | (0, (x, y)::xs) -> printList y |> ignore ; 0
        | (_, (x, y)::xs) -> askUserHelper (input-1) xs
        | _ -> failwith "shouldn't happen. Userhelper\n"

    let drop n list =
        let rec dropHelper n l =
            match (n, l) with
            | (0, l) -> l
            | (n, x::xs) -> dropHelper (n-1) xs
            | (_, []) -> failwith "list was too short"
        if n < 0 then failwith "negative argument"
        else dropHelper n list

    let string2charlist (str: string) =
        let length = (String.length str) - 1
        let rec s2cl i acc =
            match i with
            | -1 -> acc
            | _ -> s2cl (i - 1) (str.[i]::acc)
        s2cl length []

    let checkInput input = List.forall (fun x -> Char.IsDigit(x)) input

    let rec askUser list n =
        let en = if n + 3 > List.length list then let diff = (n + 3) - List.length list in n + 3 - diff else n + 3
        let l = (drop n list) in dostuff l 3
        printf "Choose one of the proposed decodings from avobe (%d - %d),\nWrite NEXT for next page,\n Or write PREV to go back to the previous page: " (n + 1) (en)
        let input = System.Console.ReadLine()
        match input with
        | x when checkInput (string2charlist input) ->
            let index = ((int input) - 1) in
            match index with
            | y when y <= (List.length list) -> askUserHelper y list
            | y when y > (List.length list) -> printf "Number too big.\n" ; askUser list n
            | _ -> printf "Please type a valid number!\n" ; askUser list n
        | "NEXT" -> if n < ((List.length list) - 4) then askUser list (n+3) else askUser list n
        | "PREV" -> if n > 0 then askUser list (n-3) else askUser list n
        | _ -> printf "Please type a valid number!\n" ; askUser list n


    let runCCipher encryptedText =
        let list = cleanString encryptedText |> Array.toList
        let list2 = decipher list |> List.sortBy (fun (x, y) -> x) |> List.rev
        askUser list2 0

module FrequencyAnalysis =
    open CaesarCipher

    let count (str: string list) letter =
        let rec countHelper acc (strng: string) iterator =
            match strng with
            | strng when iterator >= String.length strng -> acc
            | strng when strng.[iterator] = letter -> countHelper (acc+1) strng (iterator+1)
            | _ -> countHelper acc strng (iterator+1)


        let rec countHelper2 strng acc =
            match strng with
            | [] -> acc
            | x::xs -> countHelper acc x 0 |> countHelper2 xs

        countHelper2 str 0


    let strLength strList = List.fold (fun total n -> total + String.length n) 0 strList

    let findFreq (str: string list) allChars =
        let length = strLength str
        let rec helper acc chars =
            match chars with
            | [] -> acc
            | x::xs -> let freq = double (count str x) / double length in helper ((x, freq)::acc) xs
        helper [] allChars



    let strList2chrList (str: string list) =
        let rec countHelper acc (strng: string) iterator =
            match strng with
            | _ when iterator >= String.length strng -> acc
            | _ -> countHelper (strng.[iterator]::acc) strng (iterator+1)


        let rec countHelper2 strng acc =
            match strng with
            | [] -> acc
            | x::xs -> countHelper acc x 0 |> countHelper2 xs

        countHelper2 str []


    let charText readLines = strList2chrList readLines |> List.rev


    let replace charList letter2replace letterWith = List.fold (fun init letter -> if letter = letter2replace then letterWith :: init else letter :: init) [] charList


    let rec getChar char tList =
        match tList with
        | [] -> '_'
        | (x, (y,z))::xs when y = char -> x
        | p::qs -> getChar char qs
        | _ -> failwith "shouldn't happen - print chars\n"

    let printAndTranslateCharList charList tupleList = List.map (fun ch -> printf "%c" (getChar ch tupleList); charList) charList

    let getTranslatedCharList charList tupleList = List.fold (fun init ch -> (getChar ch tupleList) :: init) [] charList

    let charlist2string cl = List.fold (fun init ch -> init + ch.ToString()) "" cl


    let swap list char2replace charWith =
        let rec swapHelper lst acc =
            match lst with
            | [] -> acc
            | x::xs when x = char2replace -> swapHelper xs (charWith::acc)
            | x::xs when x = charWith -> swapHelper xs (char2replace::acc)
            | x::xs -> swapHelper xs (x::acc)
        swapHelper list  [] |> List.rev


    let printList list =
        let rec plhelper list =
            match list with
            | [] -> printf "|" ; ()
            | x::xs -> printf "%c" x ; plhelper xs
        match list with
        | x::xs -> printf "|%c" x ; plhelper xs
        | _ -> failwith "error - printlist\n"

    let runWC readLines zipped =
            let x = getTranslatedCharList (charText readLines) zipped |> List.rev in let n = Array.toList (cleanString (charlist2string x))
            let result = n |>  Seq.countBy id |> Seq.toList |> List.sortBy (fun (x, y) -> y) |> List.rev
            printf "%A" result

    let rec runFA (replaceWith: char list) zip mostFrequent readLines =
        runWC readLines zip
        printf "\n\nCurrent alphabet permutation (all characters between -> |...| )\n"
        printList replaceWith
        printf "\n\n\n"
        printAndTranslateCharList (charText readLines) zip |> ignore
        printf "\nDone? If so write -> EXIT (otherwise anything): "
        let answer = Console.ReadLine()
        match answer with
        | "EXIT" -> ()
        | _ -> printf "\n\n\nLetter 1 to swap: "
               let answer1 = char (Console.Read())
               Console.ReadLine() |> ignore
               printf "\nLetter 2 to swap: "
               let answer2 = char (Console.Read())
               Console.ReadLine() |> ignore
               if List.exists (fun x -> x = answer1) replaceWith && List.exists (fun x -> x = answer2) replaceWith
               then let newList = swap replaceWith answer1 answer2 in runFA newList (List.zip newList mostFrequent) mostFrequent readLines
               else printf "You can only use letters that are present in the alphabet permutation otherwise it will break the data!\n\n"; runFA replaceWith zip mostFrequent readLines

module BreakingTheCipher =
    open FrequencyAnalysis
    let offsetChar character offset =
        char (int character + offset)
    let printChars charList = List.map (fun ch ->  printf "%c" ch; ch) charList

    let drop n list =
        let rec dropHelper n l =
            match (n, l) with
            | (0, l) -> l
            | (n, x::xs) -> dropHelper (n-1) xs
            | (_, []) -> []
        if n < 0 then failwith "Debug error - drop negative argument"
        else dropHelper n list

    let encrypt (offset: int array) length input =
        let rec encrypt1Length offst inputList outputList iterator =
            match (iterator, inputList) with
            | (0, _) -> outputList
            | (_, []) -> outputList
            | (_, x::xs) -> encrypt1Length offst xs ((offsetChar x offst)::outputList) (iterator-1)
            | _ -> failwith "debug error - encrypt1length\n"

        let rec encryptHelper1 length acc inputList i =
            match inputList with
            | [] -> acc
            | _ ->  let index = i%length in let newacc = encrypt1Length offset.[index] inputList acc length
                    encryptHelper1 length newacc (drop length inputList) (i+1)

        encryptHelper1 length [] input 0 |> List.rev

    let decrypt (offset: int array) length input =
        let invertOffset offset = List.map (fun x -> x * -1) offset
        let decryptOffset = invertOffset (Array.toList offset) |> List.toArray in
        encrypt decryptOffset length input


    open CaesarCipher
    let getData filename =
        let rec getOffsetKey acc =
            printf "Enter offset or write DONE: "
            let input = Console.ReadLine()
            match input with
            | "DONE" -> if List.isEmpty acc
                        then printf "\nCant have an empty offsetkey\n"; getOffsetKey acc
                        else let res = List.rev acc in
                             printf "\nOffsetKey: "; List.map (fun x -> printf "%d " x; x) res |> ignore; printf "\n\n"; List.toArray res
            | _ -> if (input.[0] = '-' || Char.IsDigit(input.[0])) && (checkInput (string2charlist input.[1..]))
                    then getOffsetKey (int input::acc)
                    else printf "\nOnly numerical values allowed\n"; getOffsetKey acc
        let offsetKey = getOffsetKey []
        let lengthKey = Array.length offsetKey
        let readLines = Array.toList (File.ReadAllLines(filename)) |> strList2chrList |> List.rev
        (lengthKey, readLines, offsetKey)

    let encrypt1 filename =
        let data = getData filename
        match data with
        | (lengthKey, readLines, offsetKey) -> encrypt offsetKey lengthKey readLines |> printChars |> ignore

    let decrypt1 filename =
        let data = getData filename
        match data with
        | (lengthKey, encrypted, offsetKey) -> decrypt offsetKey lengthKey encrypted |> printChars |> ignore

    let encryptThenDecrypt4Testing filename =
        let data = getData filename
        match data with
        | (lengthKey, readlines, offsetKey) -> let encrypted = (encrypt offsetKey lengthKey readlines) |> printChars in
                                               decrypt offsetKey lengthKey encrypted |> printChars |> ignore


open CaesarCipher
open FrequencyAnalysis
open BreakingTheCipher
let getFilename () =
    printf "Enter filename of file to use: "
    Console.ReadLine()

let Caesar filename =
    //Caesar cipher
    let encryptedText = File.ReadAllText(filename)
    runCCipher encryptedText |> ignore

let FrequencyAnalysis filename =
    let getChars path =
        let helper (streamReader : StreamReader) : option<char> =
            let x = streamReader.Peek() in
            match x with
            | x when x > -1 -> Some (char (streamReader.Read()))
            | _ -> None
        let fp = File.OpenText(path)
        let rec readFromFile (acc: char list) filePointer =
            match (helper filePointer) with
            | Some(x) -> readFromFile (x::acc) filePointer
            | None ->   filePointer.Close()
                        acc
        readFromFile [] fp
    //Frequency analysis
    //final permutation
    //[' ';'E';'T';'O';'A';'S';'N';'H';'I';'D';'R';'L';'P';'U';'F';'W';'.';'Y';'G';'C';'M';'B';',';'K';''';'V';'X';';';'J';'-';'Z';'Q';'!';'?';'(';')']
    let readLines = (Array.toList (System.IO.File.ReadAllLines(filename)))
    //allChars will always be in this order
    let allChars = ['A';'B';'C';'D';'E';'F';'G';'H';'I';'J';'K';'L';'M';'N';'O';'P';'Q';'R';'S';'T';'U';'V';'W';'X';'Y';'Z';'.';',';';';'(';')';'?';'!';''';' ';'-']
    let mostFrequent = List.sortBy (fun (x,y) -> y) (findFreq readLines allChars) |> List.rev
    //replacewith is changed when using the program (needs to be read from file)
    printf "Select file to read initial alphabet permutation from. "
    let apfilename = getFilename ()
    let replacewith = getChars apfilename |> List.rev
    let zipped = List.zip replacewith mostFrequent
    runFA replacewith zipped mostFrequent readLines



let rec BeatingFrequencyAnalysis () =
    //Beating simple frequency analysis
    let filename = getFilename ()
    printf "\n1 - Encrypt\n"
    printf "2 - Decrypt\n"
    printf "3 - Encrypt and then decrypt (test)\n"
    printf "4 - Exit\n\n"
    printf ">"
    let answer = char (Console.Read())
    Console.ReadLine() |> ignore
    match answer with
    | '1' -> printf "Encrypt\n\n"; encrypt1 filename; printf "\n\n\n\n\n\n"; BeatingFrequencyAnalysis ()
    | '2' -> printf "Decrypt\n\n"; decrypt1 filename; printf "\n\n\n\n\n\n"; BeatingFrequencyAnalysis ()
    | '3' -> printf "Encrypt and then decrypt, testing.\n\n"; encryptThenDecrypt4Testing filename; printf "\n\n\n\n\n\n"; BeatingFrequencyAnalysis ()
    | '4' -> ()
    | _ ->  printf "\n\n\n\n\n\n"; BeatingFrequencyAnalysis ()


[<EntryPoint>]
let rec main _ =
    //files that we used
    (*let caesarcf = "../../../encryptedText.txt"
    let frequencyaf = "../../../text2.txt"
    let alphabetpo = "../../../alphabetPermutationOriginal.txt"
    let beatingfrequencyaf = "../../../text3.txt"*)

    printf "1 - Caesar cipher\n"
    printf "2 - Frequency analysis\n"
    printf "3 - Beating simple Frequency analysis\n"
    printf "4 - Exit\n\n"
    printf ">"
    let answer = char (Console.Read())
    Console.ReadLine() |> ignore
    match answer with
    | '1' -> printf "Caesar cipher\n\n"; getFilename () |> Caesar; printf "\n\n\n\n\n\n"; main [|""|]
    | '2' -> printf "Frequency analysis\n\n"; getFilename () |> FrequencyAnalysis; printf "\n\n\n\n\n\n"; main [|""|]
    | '3' -> printf "Beating simple Frequency analysis\n\n"; BeatingFrequencyAnalysis (); printf "\n\n\n\n\n\n"; main [|""|]
    | '4' -> 0
    | _ ->  printf "\n\n\n\n\n\n"; main [|""|]
