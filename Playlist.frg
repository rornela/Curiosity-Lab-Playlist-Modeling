#lang forge

/*
 * Perceptually Random Music Shuffling Algorithm
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


// Artists who create songs
sig Artist {}

// Albums which contain songs
sig Album {
    albumArtist: one Artist       // Each album belongs to one artist
}


// Songs are the primary entities in our model
sig Song {
    artist: one Artist,      // Each song has exactly one artist
    album: one Album,        // Each song belongs to exactly one album
    genre: one Genre,        // Each song has exactly one primary genre
    energy: one Int,         // Represents song energy/tempo on scale 1-10
    playCount: one Int,      // How many times the song has been played
    lastPlayed: lone Int     // When the song was last played (time units)
}

// Music genres
sig Genre {}

// A playlist represents a shuffled sequence of songs
sig Playlist {
    // Maps position to song (partial function since not all positions may be filled)
    sequence: pfunc Int -> Song,
    
    // Current playback position
    currentPosition: one Int
}


// ------------ Well-formedness Predicates ------------

// Ensure all model elements follow basic well-formedness constraints
pred wellformed {
    // All songs have valid attribute values
    all s: Song | {
        // Energy cannot be negative 
        s.energy >= 0
        
        // Play count cannot be negative
        s.playCount >= 0
        
        // Last played must be non-negative if present
        some s.lastPlayed implies s.lastPlayed >= 0
        
        // Artist on song matches artist on album (consistency constraint)
        s.artist = s.album.albumArtist
    }
    
    // All playlists have valid properties
    all p: Playlist | {
        // Ensure no negative indices in sequence
        all i: Int | {
            some p.sequence[i] implies i >= 0

        }
        // Ensure sequence is contiguous (no gaps)
        all i: Int | {
            (i >= 0 and i < (#p.sequence)) implies some p.sequence[i]
        }
        
        // Current position must be valid
        p.currentPosition >= 0 and p.currentPosition < (#p.sequence)
    }
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

// Ensures no consecutive songs by the same artist
pred noConsecutiveSameArtist[playlist: Playlist] {
    all i: Int | {
        // For each valid position with a next position
        (i >= 0 and i < subtract[#{s: Song | some idx: Int | playlist.sequence[idx] = s}, 1]) implies {
            let s1 = playlist.sequence[i], 
                s2 = playlist.sequence[add[i, 1]] |
                not sameArtist[s1, s2]
        }
    }
}
// No more than N consecutive songs of the same genre
pred limitConsecutiveSameGenre[playlist: Playlist, n: Int] {
    all i: Int | {
        (i >= 0 and add[i, n] < #playlist.sequence) implies {
            some j: Int | {
                i <= j and j <= add[i, n] and
                not sameGenre[playlist.sequence[i], playlist.sequence[j]]
            }
        }
    }
}

// Space out songs from the same album
pred spaceOutAlbumSongs[playlist: Playlist, minDistance: Int] {
    all i, j: Int | {
        (i != j and i >= 0 and j >= 0 and
         i < #playlist.sequence and j < #playlist.sequence and
         sameAlbum[playlist.sequence[i], playlist.sequence[j]]) implies {
            abs[subtract[i, j]] >= minDistance
        }
    }
}

// Maintain good energy flow (no extreme jumps)
pred smoothEnergyTransition[playlist: Playlist, maxJump: Int] {
    all i: Int | {
        (i >= 0 and i < subtract[(#playlist.sequence), 1] and #playlist.sequence > 1 ) implies {
            let s1 = playlist.sequence[i], 
                s2 = playlist.sequence[add[i, 1]] |
                energyDifference[s1, s2] <= maxJump
        }
    }
}

// Space out recently played songs (they should appear later in the playlist)
pred spaceOutRecentlyPlayed[playlist: Playlist, recencyThreshold: Int] {
    all s: Song | {
        s.lastPlayed > recencyThreshold implies {
            // If song was recently played, it should be later in the playlist
            (s in playlist.sequence[Int]) implies {
                min[{i: Int | playlist.sequence[i] = s}] > divide[(#playlist.sequence), 2]
            }
        }
    }
}

// Balance between popular and less-played songs
pred balancedExposure[playlist: Playlist] {
    // Define what we consider "popular" and "less played" songs based on playCount
    // These thresholds are intentionally chosen to work with small integer scopes
    let popularThreshold = 1,
        lessPlayedThreshold = 0 | {
        
        // REQUIREMENT 1: Include diversity in song popularity
        // Ensure at least one less-played song appears in the playlist
        some s: Song | {
            s.playCount <= lessPlayedThreshold
            s in playlist.sequence[Int]
        }
        
        // Ensure at least one popular song appears in the playlist
        some s: Song | {
            s.playCount >= popularThreshold
            s in playlist.sequence[Int]
        }
        
        // REQUIREMENT 2: Distribute popular songs throughout the playlist
        // Rather than front-loading all popular songs, we want some less-popular
        // songs in the first third and some popular songs in the last third
        
        // Ensure at least one less-popular song appears in the first third
        some i: Int | {
            i >= 0
            i < divide[#playlist.sequence, 3]
            some playlist.sequence[i]
            (playlist.sequence[i]).playCount <= lessPlayedThreshold
        }
        
        // Ensure at least one popular song appears in the last third
        some j: Int | {
            j >= divide[multiply[#playlist.sequence, 2], 3]
            j < #playlist.sequence
            some playlist.sequence[j]
            (playlist.sequence[j]).playCount >= popularThreshold
        }
    }
}

// Ensure playlist contains no duplicates
pred noDuplicates[playlist: Playlist] {
    all i, j: Int | {
        (i != j and i >= 0 and j >= 0 and 
         i < #playlist.sequence and j < #playlist.sequence) implies {
            playlist.sequence[i] != playlist.sequence[j]
        }
    }
}

// ------------ Main Algorithm Predicate ------------

// The main perceptually random shuffle algorithm
pred perceptuallyRandomShuffle[playlist: Playlist] {
    
    // Basic constraint: no song repeats
    noDuplicates[playlist]
    
    /*
    -- CONSTRAINTS ARE CHANGED FOR RESTRICTED NUMBER OF DATA, LARGER INTS AND DATA SETS REQUIRED 
    -- TO TEST MORE
    */

    // Artist variety constraints
    noConsecutiveSameArtist[playlist]
    
    // Album spacing constraints
    spaceOutAlbumSongs[playlist, 1]
    
    // Genre constraints - limit consecutive same genre to 
    limitConsecutiveSameGenre[playlist, 1]
    
    // Flow constraints - maintain smooth energy transitions
    smoothEnergyTransition[playlist, 10]
    
    // Exposure constraints - balance popular and less-played
    balancedExposure[playlist]
}

// ------------ Metrics and Comparison Predicates ------------

// True randomness (which might cluster artists)
pred trulyRandomShuffle[playlist: Playlist] {
    // Only enforce that songs don't repeat
    noDuplicates[playlist]
    // Everything else is unconstrained
}

// User satisfaction model
pred userSatisfied[playlist: Playlist] {
    // Baseline: perceptually random
    perceptuallyRandomShuffle[playlist]
    
    // Additional constraints that model user satisfaction
    // Favorite songs (high play count) appear but not too close together
    all s: Song, i, j: Int | {
        // Define conditions for high play count songs
        (s.playCount > 10 and 
         i >= 0 and j >= 0 and 
         i < #playlist.sequence and 
         j < #playlist.sequence and
         playlist.sequence[i] = s and 
         playlist.sequence[j] = s) implies {
            abs[i - j] > divide[#playlist.sequence, 3]
        }
    }
}

// Detect streaks (useful for evaluating perceived randomness)
pred detectArtistStreak[playlist: Playlist, streakLength: Int] {
    some i: Int | {
        (i >= 0 and add[i, subtract[streakLength, 1]] < #playlist.sequence) implies {
            all j: Int | {
                (j >= i and j < add[i, streakLength]) implies {
                    sameArtist[playlist.sequence[i], playlist.sequence[j]]
                }
            }
        }
    }
}

// ------------ Test Runs ------------

run {
    some p1: Playlist | {
        wellformed
        perceptuallyRandomShuffle[p1]
        
    }
    
} for 10 Song, 10 Artist, 10 Album, 10 Genre, 6 Int

// Find an instance of our perceptually random shuffle
run {
    some p1: Playlist | {
        wellformed
        perceptuallyRandomShuffle[p1]
        
    }
} for 8 Song, 4 Artist, 4 Album, 3 Genre, 6 Int

// Compare with truly random shuffle
run {
    some p1, p2: Playlist | {
        trulyRandomShuffle[p1]
        perceptuallyRandomShuffle[p2]
        #p1.sequence = #p2.sequence
        
        // Show that true randomness permits artist streaks while our algorithm doesn't
        detectArtistStreak[p1, 2]
        not detectArtistStreak[p2, 2]
    }
} for 8 Song, 4 Artist, 4 Album, 3 Genre, 5 Int

// // Test for user satisfaction
// run {
//     some p: Playlist | userSatisfied[p]
// } for 8 Song, 4 Artist, 4 Album, 3 Genre, 5 Int

// // Verify no consecutive same artist in perceptual shuffle
// test expect {
//     all p: Playlist | 
//         perceptuallyRandomShuffle[p] implies not detectArtistStreak[p, 2]
// } is sat

// // Verify that true randomness can produce artist streaks
// test expect {
//     some p: Playlist | {
//         trulyRandomShuffle[p] and detectArtistStreak[p, 2]
//     }
// } is sat