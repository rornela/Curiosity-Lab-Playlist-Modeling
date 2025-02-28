# Curiosity Lab Playlist Modeling

Perceptually Random Music Shuffling
Project Objective
This project models a perceptually random music shuffling algorithm that attempts to bridge the gap between true randomness and perceived randomness in music playlists. While a truly random shuffle might place multiple songs from the same artist back-to-back or create jarring transitions between high and low energy songs, users typically perceive this as "not random" or unsatisfying.
Our model explores this discrepancy by implementing constraints that create more satisfying listening experiences. The algorithm enforces rules such as:

No consecutive songs by the same artist
Spacing out songs from the same album
Maintaining good energy/tempo flow between songs
Balancing popular songs with less-played tracks
Creating natural-feeling genre transitions

The project demonstrates how these constraints lead to playlists that feel more "random" to users than truly random shuffles, despite being more constrained.
Model Design and Visualization
Model Design
The model centers around creating playlists that satisfy various musicological constraints. We've designed the model with several key components:

Basic Music Library Entities: Artists, Albums, Genres, and Songs with various attributes
Well-formedness Rules: Ensuring basic correctness of the music library and playlists
Shuffle Algorithm Constraints: Various rules that control how songs are sequenced
Comparison Predicates: Tools to compare different shuffling approaches (perceptual vs. truly random)

Our model uses Forge's ability to find instances satisfying multiple constraints simultaneously, effectively "solving" for a playlist ordering that meets all our perceptual randomness criteria.
Visualization
There are no custom visualizations due to time coonstraints but when viewing instances in the Sterling visualizer, you'll see:

Songs: Each with attributes like artist, album, genre, energy level, play count, and whether it was recently played
Playlists: Showing the sequence of songs with their positions

The visualization helps demonstrate how the perceptually random algorithm creates playlists that avoid patterns like consecutive songs by the same artist or dramatic energy shifts, while still maintaining variety.
The default Sterling visualization I felt was sufficient for this model, as the relationships between entities are clear in the table format.

Signatures and Predicates
Signatures

Artist: Represents a musical artist
Album: Represents a collection of songs with a single albumArtist
Genre: Represents a musical genre
Song: The primary entities in our model with the following attributes:

artist: The performer (must match album's artist)
album: The album it belongs to
genre: The primary genre
energy: Integer value representing the song's energy/tempo (full int scale, -8-7)
playCount: How many times the song has been played
recentlyPlayed: Whether the song was recently played (-1 if not, 1 if yes)

Playlist: Represents a shuffled sequence of songs with:

sequence: Maps position (Int) to song
lastIndex: The index of the last song in the playlist

Key Predicates

wellformedElements: Ensures all elements follow basic correctness rules (album artist matches song artist, non-negative play counts, etc.)
wellformedPlaylist: Ensures playlists have songs in sequential positions without gaps
Helper predicates like sameArtist, sameAlbum, sameGenre and function energyDifference to support constraint checking
Constraint predicates:

noDuplicates: Ensures no song appears twice in a playlist
noConsecutiveSameArtist: Prevents consecutive songs by the same artist
limitConsecutiveSameGenre: Prevents more than 4 consecutive songs in the same genre
noConsecutiveSameAlbum: Prevents consecutive songs from the same album
smoothEnergyTransition: Ensures energy level changes between consecutive songs aren't too dramatic
spaceOutRecentlyPlayed: Places recently played songs later in the playlist
balancedExposure: Ensures both popular and less-played songs appear throughout the playlist

Algorithm predicates:

perceptuallyRandomShuffle: Combines all constraints to create a perceptually random playlist
trulyRandomShuffle: Simple shuffle with only basic constraints, used for comparison
userSatisfied: Extends perceptual randomness with additional user satisfaction metrics

Testing
Our testing approach focuses on verifying both the foundational aspects of the model and the specific behavior of our perceptually random algorithm. The test suite (in playlist_tests.frg) includes:
Basic Wellformedness Tests

modelNotVacuous, playlistNotVacuous: Verify the model itself can be satisfied
negativePlayCountTest, artistMismatchTest: Confirm basic constraints function correctly
playlistGapsTest, lastIndexTest: Verify playlist structure rules

Individual Constraint Tests

noDuplicatesTest: Verifies duplicate songs are rejected
noConsecutiveSameArtistTest: Confirms consecutive songs by the same artist are disallowed
limitConsecutiveSameGenreForbidsTest: Verifies 5+ consecutive songs of the same genre are prohibited
smoothEnergyTransitionTest: Checks that large energy jumps are prevented
spaceOutRecentlyPlayedTest: Ensures recently played songs come after non-recently played ones
balancedExposureTest: Verifies distribution of popular and less-played songs

Algorithm Behavior Tests

perceptuallyRandomShuffleSat: Confirms the full algorithm can be satisfied
trulyRandomAllowsSameArtist: Shows truly random shuffling permits artist streaks
perceptuallyRandomMoreConstrained: Demonstrates perceptual randomness is more constrained than true randomness
userSatisfiedTest: Tests our extended user satisfaction model

Property Verification

perceptualRandomImpliesNoDuplicates, etc.: Formally verify that the main algorithm implies all its constituent constraints

This comprehensive testing approach ensures our model correctly captures the behavior of perceptually random music shuffling algorithms and demonstrates their advantages over truly random approaches.
Implementation Notes
The model is implemented using Forge, and attempts to capture various quantifiable values
attributed to music that real music streaming platforms use:

Expressiveness: The model captures nuanced concepts like energy flow and popularity balance
Scalability: Constraints are designed to work within reasonable bounds in Forge (small integer scopes, 4 INT)
Clarity: Predicates are structured to clearly communicate their purpose

Some implementation challenges we addressed:

Originally attempted to parameterize genre streak length but simplified to a fixed limit of 4
Refined the recently played logic to improve playlist variety
Carefully designed integer thresholds for energy and popularity to work with limited Forge integer ranges

The model demonstrates how formal methods can be applied to real-world user experience problems, providing insights into the balance between true randomness and perceived randomness in music consumption.
