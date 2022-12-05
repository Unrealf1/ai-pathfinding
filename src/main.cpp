#include "raylib.h"
#include <functional>
#include <iterator>
#include <vector>
#include <limits>
#include <cmath>
#include "math.h"
#include "dungeonGen.h"
#include "dungeonUtils.h"
#include <algorithm>
#include <cstdint>
#include <unordered_set>
#include <ranges>

namespace rng = std::ranges;
using std::views::transform;

bool contains(const auto& range, const auto& element) {
    return rng::find(range, element) != range.end();
}

size_t g_height;

template<typename T>
static size_t coord_to_idx(T x, T y, size_t w)
{
  return std::min(size_t(y) * w + size_t(x), w * g_height - 1);
}

static void draw_nav_grid(const char *input, size_t width, size_t height)
{
  for (size_t y = 0; y < height; ++y)
    for (size_t x = 0; x < width; ++x)
    {
      char symb = input[coord_to_idx(x, y, width)];
      Color color = GetColor(symb == ' ' ? 0xeeeeeeff : symb == 'o' ? 0x7777ffff : 0x222222ff);
      DrawPixel(int(x), int(y), color);
    }
}

static void draw_path(std::vector<Position> path, Color color)
{
  for (const Position &p : path)
    DrawPixel(p.x, p.y, color);
}

static void draw_path(std::vector<Position> path, uint32_t color = 0x44000088)
{
  draw_path(path, GetColor(color));
}

static std::vector<Position> reconstruct_path(std::vector<Position> prev, Position to, size_t width)
{
  Position curPos = to;
  std::vector<Position> res = {curPos};
  while (prev[coord_to_idx(curPos.x, curPos.y, width)] != Position{-1, -1})
  {
    curPos = prev[coord_to_idx(curPos.x, curPos.y, width)];
    res.insert(res.begin(), curPos);
  }
  return res;
}

static std::vector<Position> find_path_a_star(const char *input, size_t width, size_t height, Position from, Position to)
{
  if (from.x < 0 || from.y < 0 || from.x >= int(width) || from.y >= int(height))
    return std::vector<Position>();
  size_t inpSize = width * height;

  std::vector<float> g(inpSize, std::numeric_limits<float>::max());
  std::vector<float> f(inpSize, std::numeric_limits<float>::max());
  std::vector<Position> prev(inpSize, {-1,-1});

  auto getG = [&](Position p) -> float { return g[coord_to_idx(p.x, p.y, width)]; };
  auto getF = [&](Position p) -> float { return f[coord_to_idx(p.x, p.y, width)]; };

  auto heuristic = [](Position lhs, Position rhs) -> float
  {
    return sqrtf(square(float(lhs.x - rhs.x)) + square(float(lhs.y - rhs.y)));
  };

  g[coord_to_idx(from.x, from.y, width)] = 0;
  f[coord_to_idx(from.x, from.y, width)] = heuristic(from, to);

  std::vector<Position> openList = {from};
  std::vector<Position> closedList;

  while (!openList.empty())
  {
    size_t bestIdx = 0;
    float bestScore = getF(openList[0]);
    for (size_t i = 1; i < openList.size(); ++i)
    {
      float score = getF(openList[i]);
      if (score < bestScore)
      {
        bestIdx = i;
        bestScore = score;
      }
    }
    if (openList[bestIdx] == to)
      return reconstruct_path(prev, to, width);
    Position curPos = openList[bestIdx];
    openList.erase(openList.begin() + bestIdx);
    if (std::find(closedList.begin(), closedList.end(), curPos) != closedList.end())
      continue;
    size_t idx = coord_to_idx(curPos.x, curPos.y, width);
    DrawPixel(curPos.x, curPos.y, Color{uint8_t(g[idx]), uint8_t(g[idx]), 0, 100});
    closedList.emplace_back(curPos);
    auto checkNeighbour = [&](Position p)
    {
      // out of bounds
      if (p.x < 0 || p.y < 0 || p.x >= int(width) || p.y >= int(height))
        return;
      size_t idx = coord_to_idx(p.x, p.y, width);
      // not empty
      if (input[idx] == '#')
        return;
      float weight = input[idx] == 'o' ? 10.f : 1.f;
      float gScore = getG(curPos) + 1.f * weight; // we're exactly 1 unit away
      if (gScore < getG(p))
      {
        prev[idx] = curPos;
        g[idx] = gScore;
        f[idx] = gScore + heuristic(p, to);
      }
      bool found = std::find(openList.begin(), openList.end(), p) != openList.end();
      if (!found)
        openList.emplace_back(p);
    };
    checkNeighbour({curPos.x + 1, curPos.y + 0});
    checkNeighbour({curPos.x - 1, curPos.y + 0});
    checkNeighbour({curPos.x + 0, curPos.y + 1});
    checkNeighbour({curPos.x + 0, curPos.y - 1});
  }
  // empty path
  return std::vector<Position>();
}

std::vector<std::vector<Position>> find_path_ara_star(
        const char *input,
        size_t width,
        size_t height,
        Position from,
        Position to
)
{
  {
    auto fidx = coord_to_idx(from.x, from.y, width);
    auto tidx = coord_to_idx(to.x, to.y, width);

    if (input[fidx] == '#' || input[tidx] == '#') {
        return {};
    }
  }

  std::vector<std::vector<Position>> result;
  auto inpSize = width * height;
  auto distance = [](Position lhs, Position rhs) -> float
  {
    return sqrtf(square(float(lhs.x - rhs.x)) + square(float(lhs.y - rhs.y)));
  };
  auto heuristic = [&](Position point) {
    return distance(point, to);
  };

  float epsilon = 15.0f;

  std::vector<float> g(inpSize, std::numeric_limits<float>::infinity());
  std::vector<Position> open = { from };
  std::vector<Position> closed;
  std::vector<Position> incons;

  auto getG = [&](Position p) -> float& { return g[coord_to_idx(p.x, p.y, width)]; };
  auto fval = [&](auto point) {
    return getG(point) + epsilon * heuristic(point);
  };


  getG(from) = 0;

  auto each_succ = [&](const Position& pos, auto callback) {
    std::vector<Position> neighboors = {
        {pos.x + 1, pos.y},
        {pos.x - 1, pos.y},
        {pos.x, pos.y + 1},
        {pos.x, pos.y - 1}
    };
    auto view = neighboors | rng::views::filter([&](const Position& pos) {
        bool valid = pos.x < width && pos.y < height && pos.x > 0 && pos.y > 0;
        if (valid) {
            return input[coord_to_idx(pos.x, pos.y, width)] != '#';
        }
        return false;
    });
    rng::for_each(view, callback);
  };

  auto ImprovePath = [&]{
    std::vector<Position> prev(inpSize, {-1, -1});
    while(!open.empty() && fval(to) > rng::min(open | transform(fval))) {
        auto min = rng::min_element(open, {}, fval);
        auto current = *min;
        auto current_idx = coord_to_idx(current.x, current.y, width);
        closed.push_back(current);
        open.erase(min);
        each_succ(current, [&](const Position& succ) {
            auto idx = coord_to_idx(succ.x, succ.y, width);
            auto dist = distance(succ, current);
            if (input[idx] == 'o') {
                dist += 10.0f;
            }
            float reliable_way = getG(current) + dist;
            if (getG(succ) > reliable_way) {
                getG(succ) = reliable_way;
                prev[idx] = current;
                if (!contains(closed, succ)) {
                    open.push_back(succ);
                } else {
                    incons.push_back(succ);
                }
            }
        });
    }
    return reconstruct_path(prev, to, width);
  };
  
  auto get_new_epsilon = [&]{
    auto trans = transform([&](const Position& value) {
        return getG(value) + heuristic(value);        
    });
    if (incons.empty()) {
        return getG(to) / rng::min(open | trans);
    }
    return getG(to) / std::min(rng::min(open | trans), rng::min(incons | trans));
  };

  result.push_back(ImprovePath());
  
  float epsilon2 = std::min(epsilon, get_new_epsilon());
  while (epsilon2 > 1.0f) {
    epsilon *= 0.8f;
    rng::copy(incons, std::back_inserter(open));
    closed.clear();
    incons.clear();
    result.push_back(ImprovePath());
    epsilon2 = std::min(epsilon, get_new_epsilon());
  }

  return result;
}


void draw_nav_data(const char *input, size_t width, size_t height, Position from, Position to)
{
  draw_nav_grid(input, width, height);
  std::vector<Position> path = find_path_a_star(input, width, height, from, to);
  draw_path(path);
}

Color get_color(size_t idx) {
    auto fidx = float(idx);
    auto s = sinf(fidx);
    auto c = cosf(fidx);
    auto cs = sinf(fidx * fidx) + cosf(fidx * fidx);
    auto r = (s + 1.0f) / 2.0f * 255.0f;
    auto g = (c + 1.0f) / 2.0f * 255.0f;
    auto b = (cs + 1.5f) / 3.0f * 255.0f;

    auto rb = uint8_t(r);
    auto gb = uint8_t(g);
    auto bb = uint8_t(b);

    Color result = {
        .r = 10,
        .g = gb,
        .b = bb,
        .a = rb
    };
    return result;
}

void draw_nav_data_iterational(const char *input, size_t width, size_t height, Position from, Position to)
{
  draw_nav_grid(input, width, height);
  std::vector<std::vector<Position>> pathes = find_path_ara_star(input, width, height, from, to);
  for (size_t i = 0; const auto& path : pathes) {
      draw_path(path, get_color(i));
      ++i;
  }
}

int main(int /*argc*/, const char ** /*argv*/)
{
  int width = 720;
  int height = 620;
  InitWindow(width, height, "w3 AI MIPT");

  const int scrWidth = GetMonitorWidth(0);
  const int scrHeight = GetMonitorHeight(0);
  if (scrWidth < width || scrHeight < height)
  {
    width = std::min(scrWidth, width);
    height = std::min(scrHeight - 150, height);
    SetWindowSize(width, height);
  }

  constexpr size_t dungWidth = 100;
  constexpr size_t dungHeight = 100;
  char *navGrid = new char[dungWidth * dungHeight];
  gen_drunk_dungeon(navGrid, dungWidth, dungHeight, 24, 100);
  spill_drunk_water(navGrid, dungWidth, dungHeight, 8, 10);

  Position from = dungeon::find_walkable_tile(navGrid, dungWidth, dungHeight);
  Position to = dungeon::find_walkable_tile(navGrid, dungWidth, dungHeight);

  Camera2D camera = { {0, 0}, {0, 0}, 0.f, 1.f };
  //camera.offset = Vector2{ width * 0.5f, height * 0.5f };
  camera.zoom = float(height) / float(dungHeight);

  SetTargetFPS(60);               // Set our game to run at 60 frames-per-second
  while (!WindowShouldClose())
  {
    // pick pos
    Vector2 mousePosition = GetScreenToWorld2D(GetMousePosition(), camera);
    Position p{int(mousePosition.x), int(mousePosition.y)};
    if (IsMouseButtonPressed(2) || IsKeyPressed(KEY_Q))
    {
      size_t idx = coord_to_idx(p.x, p.y, dungWidth);
      if (idx < dungWidth * dungHeight)
        navGrid[idx] = navGrid[idx] == ' ' ? '#' : navGrid[idx] == '#' ? 'o' : ' ';
    }
    else if (IsMouseButtonPressed(0))
    {
      Position &target = from;
      target = p;
    }
    else if (IsMouseButtonPressed(1))
    {
      Position &target = to;
      target = p;
    }
    if (IsKeyPressed(KEY_SPACE))
    {
      gen_drunk_dungeon(navGrid, dungWidth, dungHeight, 24, 100);
      spill_drunk_water(navGrid, dungWidth, dungHeight, 8, 10);
      from = dungeon::find_walkable_tile(navGrid, dungWidth, dungHeight);
      to = dungeon::find_walkable_tile(navGrid, dungWidth, dungHeight);
    }
    BeginDrawing();
      ClearBackground(BLACK);
      BeginMode2D(camera);
        g_height = dungHeight;
        draw_nav_data_iterational(navGrid, dungWidth, dungHeight, from, to);
      EndMode2D();
    EndDrawing();
  }
  CloseWindow();
  return 0;
}
