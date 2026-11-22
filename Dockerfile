FROM --platform=linux/amd64 rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml ./
COPY src ./src
ENV RUSTFLAGS="-C target-cpu=x86-64-v3"
RUN cargo build --release

FROM --platform=linux/amd64 debian:bookworm-slim
COPY --from=build /src/target/release/sessions /usr/local/bin/sessions
USER 1000
ENTRYPOINT ["/usr/local/bin/sessions"]
