#lang forge

/*
 * Perceptually Random Music Shuffling / Curation Algorithm
 * ---------------------------------------------
 * 
 * This model explores the difference between true randomness and perceived randomness
 * in music library shuffling algorithms. While a truly random shuffle might place multiple
 * songs from the same artist back-to-back, users typically perceive this as "not random."
 * 
 * Our goal is to model constraints that produce a more satisfying user experience 
 * by enforcing rules such as:
 *  - No consecutive songs by the same artist
 *  - Spacing out songs from the same album
 *  - Maintaining good energy/tempo flow between songs
 *  - Balancing popular songs with less-played tracks
 *  - Creating natural-feeling genre transitions
 */

// ------------ Basic Music Library Entities ------------

// Song's Artists

sig Artist {}

// Albums which contain songs

sig Album {
    albumArtist: one Artist
}

// Music genres
sig Genre {}

// Songs are the primary entities in our model

sig Song {
    artist: one Artist,      // Each song has exactly one artist
    album: one Album,        // Each song belongs to exactly one album
    genre: one Genre,        // Each song has exactly one primary genre
    energy: one Int,         // Represents song energy/tempo on scale 1-10
    playCount: one Int,      // How many times the song has been played
    recentlyPlayed: one Int     // Whether the song was last played 
}

// A playlist represents a shuffled sequence of songs

sig Playlist {
    // Maps position to song (partial function since not all positions may be filled)
    sequence: pfunc Int -> Song,
    lastIndex: one Int
}

// ------------ Well-formedness Predicates ------------

// Ensure all model elements follow basic well-formedness constraints
pred wellformedElements{

    all s: Song {
        // song artist should be same as song's album's artist
        s.artist = s.album.albumArtist
        // playCount not negative
        s.playCount >= 0
        // Recently played binary -1,1:
        // 1 if  within listener's recently played, -1 otherwise
        // (ex. 1 if song is within last 10 songs played, -1 otherwise)
        s.recentlyPlayed >= -1 and s. recentlyPlayed <= 1 and s.recentlyPlayed != 0 

        // No constraints on energy to allow use of all number ranges
    }
}

pred wellformedPlaylist[p: Playlist] {

    -- no songs before index 0
    all i: Int | i < 0 implies no p.sequence[i]

    -- if there's a song, either i=0 or there's something at i=1
    -- also the array is sorted:
    all i: Int | some p.sequence[i] implies {
        i = 0 or some p.sequence[subtract[i, 1]]
    }

    -- size variable reflects actual size of array    
    all i: Int | (no p.sequence[i] and 
                  some p.sequence[subtract[i, 1]]) implies {
        p.lastIndex = subtract[i, 1]
    }    
    {all i: Int | no p.sequence[i]} implies 
      {p.lastIndex = -1}

}

// ------------ Helper Predicates and Functions ------------

// Check if two songs are by the same artist
pred sameArtist[s1, s2: Song] {
    s1.artist = s2.artist
}

// Check if two songs are from the same album
pred sameAlbum[s1, s2: Song] {
    s1.album = s2.album
}

// Check if songs have the same genre
pred sameGenre[s1, s2: Song] {
    s1.genre = s2.genre
}

// Calculate absolute energy level difference between songs
fun energyDifference[s1, s2: Song]: Int {
    abs[subtract[s1.energy, s2.energy]]
}

// ------------ Shuffle Algorithm Constraints ------------

// Ensure playlist contains no duplicates
pred noDuplicates[p: Playlist] {
    all i, j: Int | {
        ((i != j and some p.sequence[i]) and some p.sequence[j] and i >= 0 and j >= 0) implies {
            p.sequence[i] != p.sequence[j]
        }
    }
}

// Ensures no consecutive songs by the same artist
pred noConsecutiveSameArtist[p: Playlist] {
    all i: Int | {
        // For each valid position with a next position
        (i >= 0 and i < subtract[#{s: Song | some idx: Int | p.sequence[idx] = s}, 1]) implies {
            let s1 = p.sequence[i], 
                s2 = p.sequence[add[i, 1]] |
                not sameArtist[s1, s2]
        }
    }
}

// Had trouble implementing logic of N limit, 
// ALWAYS RETURNING UNSAT
// too broad to enforce without being unsat?
// // LOGIC NOT WORKING 
// // No more than N consecutive songs of the same genre
// pred limitConsecutiveSameGenre[p: Playlist, n: Int] {
//     all i: Int | {
//         // If we have a sequence of n+1 songs starting at i
//         (i >= 0 and add[i, n] <= p.lastIndex) implies {
//             // There must be at least one adjacent pair with different genres
//             some j: Int | {
//                 i <= j and j < add[i, n] and  // Changed <= to 
//                 not sameGenre[p.sequence[j], p.sequence[add[j, 1]]]
//             }
//         }
//     }
// }  

// Ensures no more than 4 back-to-back songs in the same genre
pred limitConsecutiveSameGenre[p: Playlist]{
    all i: Int | {
        (i >= 0 and add[i,4] <= p.lastIndex) implies {
            not sameGenre[p.sequence[i], p.sequence[add[i, 4]]]
        }
    }
}


// Ensures no consecutive songs from the same album
pred noConsecutiveSameAlbum[p: Playlist] {
    all i: Int | {
        // For each valid position with a next position
        (i >= 0 and i < p.lastIndex) implies {
            let s1 = p.sequence[i], 
                s2 = p.sequence[add[i, 1]] |
                not sameAlbum[s1, s2]
        }
    }
}

// Maintain good energy flow (no extreme jumps)
pred smoothEnergyTransition[p: Playlist, maxJump: Int] {
    all i: Int | {
        (i >= 0 and i < p.lastIndex and p.lastIndex > 0 ) implies {
            let s1 = p.sequence[i], 
                s2 = p.sequence[add[i, 1]] |
                energyDifference[s1, s2] <= maxJump
        }
    }
}

// Space out recently played songs (they should appear later in the playlist)
pred spaceOutRecentlyPlayed[p: Playlist] {

    // ORIGINAL LOGIC PUTS RECENTLY PLAYED IN SECOND HALF, 
    // THUS LIMITING AMOUNT OF RECENTLY PLAYED SONGS
    // all s: Song | {
    //     s.recentlyPlayed > 0 implies {
    //         // If song was recently played, it should be later in the playlist
    //         // Specifically second half
    //         (s in p.sequence[Int]) implies {
    //             min[{i: Int | p.sequence[i] = s}] > divide[(p.lastIndex), 2]
    //         }
    //     }
    // }

    // Recently played songs should be played after non-recently-played songs
    all i, j: Int | {
        (some p.sequence[i] and some p.sequence[j] 
        and (p.sequence[i]).recentlyPlayed < (p.sequence[j]).recentlyPlayed) implies {
            i < j
        }
    }
}



// Balance between popular and less-played songs
pred balancedExposure[p: Playlist] {
    // Define what we consider "popular" and "less played" songs based on playCount
    // These thresholds are intentionally chosen to work with small integer scopes
    let popularThreshold = 3,
        lessPlayedThreshold = 1 | {
        
        // REQUIREMENT 1: Include diversity in song popularity
        // Ensure at least one less-played song appears in the playlist
        some s: Song | {
            s.playCount <= lessPlayedThreshold
            s in p.sequence[Int]
        }
        
        // Ensure at least one popular song appears in the playlist
        some s: Song | {
            s.playCount >= popularThreshold
            s in p.sequence[Int]
        }
        
        // REQUIREMENT 2: Distribute popular songs throughout the playlist
        // Rather than front-loading all popular songs, we want some less-popular
        // songs in the first half and some popular songs in the last half
        
        // Ensure at least one less-popular song appears in the first half
        some i: Int | {
            i >= 0
            i < divide[p.lastIndex, 2]
            some p.sequence[i]
            (p.sequence[i]).playCount <= lessPlayedThreshold
        }
        
        // Ensure at least one popular song appears in the last half
        some j: Int | {
            j >= divide[multiply[p.lastIndex, 2], 2]
            j <= p.lastIndex
            some p.sequence[j]
            (p.sequence[j]).playCount >= popularThreshold
        }
    }
}

// ------------ Main Algorithm Predicate ------------

// The main perceptually random shuffle algorithm
pred perceptuallyRandomShuffle[p: Playlist] {

    // Playlist is wellformed
    wellformedPlaylist[p]

    // Basic constraint: no song repeats
    noDuplicates[p]

    // Ensures no consecutive songs by the same artist
    noConsecutiveSameArtist[p]

    // No more than 4 consecutive songs of the same genre
    limitConsecutiveSameGenre[p]

    // Ensures no consecutive songs from the same album
    noConsecutiveSameAlbum[p]

    // Maintain good energy flow (no extreme jumps)
    smoothEnergyTransition[p, 5]

    // recently played songs should appear later in the playlist
    spaceOutRecentlyPlayed[p]

    // Balance between popular and less-played songs
    balancedExposure[p]
    
}

// ------------ Metrics and Comparison Predicates ------------

// True randomness (which might cluster artists)
pred trulyRandomShuffle[p: Playlist] {
    //welformed
    wellformedPlaylist[p]

    // Only enforce that songs don't repeat
    noDuplicates[p]
    // Everything else is unconstrained
}

// User satisfaction model
pred userSatisfied[p: Playlist] {
    // Baseline: perceptually random
    perceptuallyRandomShuffle[p]
    
    // Additional constraints that model user satisfaction
    // Favorite songs (high play count) appear but not too close together
    all s: Song, i, j: Int | {
        // Define conditions for high play count songs
        (s.playCount > 6 and 
         i >= 0 and j >= 0 and 
         i <= p.lastIndex and 
         j <= p.lastIndex and
         p.sequence[i] = s and 
         p.sequence[j] = s) implies {
            abs[i - j] > divide[p.lastIndex, 2]
        }
    }
}

// Detect streaks (useful for evaluating perceived randomness)
pred detectArtistStreak[p: Playlist, streakLength: Int] {
    some i: Int | {
        (i >= 0 and add[i, subtract[streakLength, 1]] <= p.lastIndex ) implies {
            all j: Int | {
                (j >= i and j < add[i, streakLength]) implies {
                    sameArtist[p.sequence[i], p.sequence[j]]
                }
            }
        }
    }
}


run {
    wellformedElements
    one p: Playlist | {
        perceptuallyRandomShuffle[p]
        some p.sequence[7]
    }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// ------------ Test Runs ------------

// Basic test: Generate a valid perceptually random playlist
run {
  wellformedElements
  one p: Playlist | {
    perceptuallyRandomShuffle[p]
    p.lastIndex >= 7 // Ensure we have a reasonable number of songs
  }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// Compare perceptually random with truly random shuffle
run {
  wellformedElements
  some p1, p2: Playlist | {
    trulyRandomShuffle[p1]
    perceptuallyRandomShuffle[p2]
    p1.lastIndex = p2.lastIndex // Ensure playlists are same length
    p1.lastIndex >= 7 // Ensure sufficient length to test constraints
    
    // Show that true randomness permits artist streaks
    some i: Int | {
      i >= 0 and i < p1.lastIndex and
      sameArtist[p1.sequence[i], p1.sequence[add[i, 1]]]
    }
  }
} for 2 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// Test specific constraints - Artist Constraint
run {
  wellformedElements
  one p: Playlist | {
    // Use all basic constraints except artist constraint
    wellformedPlaylist[p]
    noDuplicates[p]
    limitConsecutiveSameGenre[p]
    noConsecutiveSameAlbum[p]
    smoothEnergyTransition[p, 5]
    p.lastIndex >= 7
    
    // Require at least one streak of same artist (violating perceptual randomness)
    some i: Int | {
      i >= 0 and i < p.lastIndex and
      sameArtist[p.sequence[i], p.sequence[add[i, 1]]]
    }
  }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// Test for user satisfaction
run {
  wellformedElements
  one p: Playlist | {
    perceptuallyRandomShuffle[p]
    userSatisfied[p]
    p.lastIndex >= 7
  }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// Test energy transition constraint
run {
  wellformedElements
  one p: Playlist | {
    wellformedPlaylist[p]
    noDuplicates[p]
    noConsecutiveSameArtist[p]
    noConsecutiveSameAlbum[p]
    p.lastIndex >= 7
    
    // Show energy transitions are smooth
    all i: Int | {
      (i >= 0 and i < p.lastIndex) implies {
        energyDifference[p.sequence[i], p.sequence[add[i, 1]]] <= 5
      }
    }
  }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int

// Test recently played spacing
run {
  wellformedElements
  one p: Playlist | {
    wellformedPlaylist[p]
    noDuplicates[p]
    p.lastIndex >= 7
    
    // Enforce recently played spacing rule
    spaceOutRecentlyPlayed[p]
    
    // Make sure we have both recently played and not recently played songs
    some s1, s2: Song | {
      s1.recentlyPlayed = 1
      s2.recentlyPlayed = -1
      s1 in p.sequence[Int]
      s2 in p.sequence[Int]
    }
  }
} for 1 Playlist, 8 Song, 4 Artist, 4 Album, 4 Genre, 4 Int




