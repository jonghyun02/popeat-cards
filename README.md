# popeat-cards

POP&EAT 인스타그램 카드뉴스의 슬라이드 이미지(JPEG) 저장소입니다. Instagram API (Instagram API with Instagram Login)
공식 게시에 쓰는 공개 이미지 주소(raw.githubusercontent.com)를 제공합니다.

This public repository holds POP&EAT card images for Instagram API publishing.
The `cardnews publish` command adds only JPEG slides under `<date>/<slug>/NN.jpg` and uses their raw URLs.

- `<YYYY-MM-DD>/<post-slug>/01.jpg …` — 1080x1350 JPEG slides of one carousel post
- `_test/ping.jpg` — a tiny image used to check that raw URLs are served as `image/jpeg`
